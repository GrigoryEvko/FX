import FX1Poly.Polygraph.Computad.ModeComputad

/-! # Polygraph/TwoCategory/Amalgam/Pushout — the mode-signature pushout over a shared mode set (WP-AMALG-1)

The Wave-4 integration opener.  Seven walking-doctrine word problems have been DECIDED as standalone
`ModeComputad` presentations (adjunction, monad, idempotent monad, involution, level, KZ, free-generic).  FX's
own mode theory across the 21 graded dimensions is an AMALGAM of these doctrines: the dimensions SHARE the
kernel mode set (the same objects) but each contributes its OWN generators and relations, over DISJOINT
generator names.  This file builds the categorical substrate for that amalgam — the PUSHOUT of two finite
mode computads over a shared mode set.

## What is shipped here (each piece zero-axiom, structural, ASCII-only)

  * **`combinedModalityGenerators`** — the tagged 1-generator sum: `comp1`'s generators concatenated with
    `comp2`'s generators (endpoint-retagged across the shared-mode equality).  A component-1 generator keeps its
    index `< len1`; a component-2 generator is shifted to `len1 + j`.  The tag is thus the index range, the
    constructive analogue of a `Sum` (the free-product / coproduct-of-theories tagging).
  * **`pushoutShared`** — the combined computad `comp1 +_M comp2`: the shared mode count, the tagged generator
    sum, and the union of relations (each 2-generator retagged to mention only its component's letters).
  * **`ComputadMorphism`** + **`inclusionLeft` / `inclusionRight`** — the two coprojections, generator-wise
    injections with proven endpoint preservation (a genuine signature morphism apiece).
  * **`copairMorphism`** + **`copairMorphism_restrictsLeft` / `_restrictsRight`** — the EASY direction of the
    universal property: given two morphisms out of the components agreeing on the shared modes, the copairing
    factors them.  Proven.  The UNIQUENESS / full factoring direction is the honest deferral
    (`fxAmalg_hasSignaturePushoutUniqueness = false`).

## The mathematics (word-problem-flavoured, disjoint generators)

The governing prior art is NOT stably-infinite Nelson-Oppen (that is the SATISFIABILITY combination) but the
DISJOINT-SIGNATURE WORD-PROBLEM combination first proved by Pigozzi (1974) and re-derived by Baader-Tinelli
("Deciding the Word Problem in the Union of Equational Theories", 1998), whose sharp caveat is that combining
across a SHARED function symbol is undecidable in general (an associativity + ground-equation union encodes an
arbitrary finitely-presented semigroup).  The categorical framing is the pushout of PROPs via a distributive
law (Zanasi, Prop. 2.30) with the amalgamation property replacing stable-infiniteness (Ghilardi 2004).  Here
the two components share the MODE SET but have DISJOINT generators, so the amalgam embeds freely and the easy
direction (the copairing) is unconditional.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## Propext-free arithmetic / list plumbing

`List.length_append`, `List.length_map`, and `Nat.add_sub_cancel'` from core Init pull `propext`; the whole
substrate is propext-free, so the versions used below are re-proved by structural induction. -/

/-- `(l1 ++ l2).length = l1.length + l2.length`, propext-free (core `List.length_append` leaks `propext`). -/
theorem lengthAppend {Element : Type} (first second : List Element) :
    (first ++ second).length = first.length + second.length := by
  induction first with
  | nil => exact (Nat.zero_add second.length).symm
  | cons _ tail ih =>
      show (tail ++ second).length + 1 = (tail.length + 1) + second.length
      rw [ih, Nat.add_right_comm]

/-- `(l.map f).length = l.length`, propext-free (core `List.length_map` leaks `propext`). -/
theorem lengthMap {Source Target : Type} (mapper : Source → Target) (source : List Source) :
    (source.map mapper).length = source.length := by
  induction source with
  | nil => rfl
  | cons _ tail ih => show (tail.map mapper).length + 1 = tail.length + 1; rw [ih]

/-- `a + (b - a) = b` for `a ≤ b`, propext-free (core `Nat.add_sub_cancel'` leaks `propext`). -/
theorem addSubCancel : {smaller larger : Nat} → smaller ≤ larger → smaller + (larger - smaller) = larger
  | 0, _, _ => by rw [Nat.sub_zero, Nat.zero_add]
  | Nat.succ _, Nat.succ _, hle => by
      rw [Nat.succ_sub_succ, Nat.succ_add, addSubCancel (Nat.le_of_succ_le_succ hle)]

/-- `(a + b) - a = b`, propext-free (core `Nat.add_sub_cancel_left` leaks `propext`). -/
theorem addSubCancelLeft : (front back : Nat) → (front + back) - front = back
  | 0, back => by rw [Nat.zero_add, Nat.sub_zero]
  | Nat.succ front, back => by rw [Nat.succ_add, Nat.succ_sub_succ, addSubCancelLeft front back]

/-- `Nat.ble a b = true` from `a ≤ b`, propext-free (core `Nat.ble_eq` leaks `propext`). -/
theorem bleTrueOfLe : {smaller larger : Nat} → smaller ≤ larger → Nat.ble smaller larger = true
  | 0, _, _ => rfl
  | Nat.succ smaller, Nat.succ larger, hle => by
      show Nat.ble smaller larger = true
      exact bleTrueOfLe (Nat.le_of_succ_le_succ hle)

/-- `Nat.ble a b = false` from `b < a`, propext-free. -/
theorem bleFalseOfLt : {larger smaller : Nat} → smaller < larger → Nat.ble larger smaller = false
  | Nat.succ _, 0, _ => rfl
  | Nat.succ larger, Nat.succ smaller, hlt => by
      show Nat.ble larger smaller = false
      exact bleFalseOfLt (Nat.lt_of_succ_lt_succ hlt)

/-- `Nat.blt a b = true` from `a < b`, propext-free (the component tag's `true` case). -/
theorem bltTrueOfLt {below above : Nat} (isBelow : below < above) : Nat.blt below above = true :=
  bleTrueOfLe isBelow

/-- `Nat.blt a b = false` from `b ≤ a`, propext-free (the component tag's `false` case). -/
theorem bltFalseOfGe {above below : Nat} (isGe : below ≤ above) : Nat.blt above below = false :=
  bleFalseOfLt (Nat.lt_succ_of_le isGe)

/-- `a - len1 < len2` from `len1 ≤ a` and `a < len1 + len2`, propext-free (core
`Nat.sub_lt_left_of_lt_add` leaks `propext`) — the component-2 down-index bound. -/
theorem subLtOfLtAdd {value front back : Nat} (geFront : front ≤ value) (belowSum : value < front + back) :
    value - front < back := by
  have shifted : front + (value - front) < front + back := by rw [addSubCancel geFront]; exact belowSum
  exact Nat.lt_of_add_lt_add_left shifted

/-- Two `List.get`s at equal `.val` indices are equal — the index-representation bridge for the retag proofs. -/
theorem getValCongr {Element : Type} (list : List Element) {first second : Fin list.length}
    (valsEqual : first.val = second.val) : list.get first = list.get second :=
  congrArg list.get (Fin.ext valsEqual)

/-- `List.get` into the LEFT part of an append (index below `l1.length`), propext-free by induction on `l1`. -/
theorem getAppendLeft {Element : Type} :
    (first second : List Element) → (index : Nat) → (boundLeft : index < first.length) →
    (boundAppend : index < (first ++ second).length) →
    (first ++ second).get ⟨index, boundAppend⟩ = first.get ⟨index, boundLeft⟩
  | _ :: _, _, 0, _, _ => rfl
  | head :: tail, second, Nat.succ innerIndex, boundLeft, boundAppend => by
      show (tail ++ second).get ⟨innerIndex, _⟩ = tail.get ⟨innerIndex, _⟩
      exact getAppendLeft tail second innerIndex
        (Nat.lt_of_succ_lt_succ boundLeft) (Nat.lt_of_succ_lt_succ boundAppend)

/-- `List.get` into the RIGHT part of an append (index `l1.length + index`), propext-free. -/
theorem getAppendRight {Element : Type} (second : List Element) (index : Nat) (boundRight : index < second.length) :
    (first : List Element) → (boundAppend : first.length + index < (first ++ second).length) →
    (first ++ second).get ⟨first.length + index, boundAppend⟩ = second.get ⟨index, boundRight⟩
  | [], boundAppend =>
      getValCongr (([] : List Element) ++ second) (first := ⟨0 + index, boundAppend⟩)
        (second := ⟨index, boundRight⟩) (Nat.zero_add index)
  | head :: tail, boundAppend => by
      have valEq : (head :: tail).length + index = (tail.length + index) + 1 :=
        Nat.add_right_comm tail.length 1 index
      have boundSucc : (tail.length + index) + 1 < (head :: tail ++ second).length := valEq ▸ boundAppend
      calc (head :: tail ++ second).get ⟨(head :: tail).length + index, boundAppend⟩
          = (head :: tail ++ second).get ⟨(tail.length + index) + 1, boundSucc⟩ :=
              getValCongr (head :: tail ++ second) valEq
        _ = (tail ++ second).get ⟨tail.length + index, Nat.lt_of_succ_lt_succ boundSucc⟩ := rfl
        _ = second.get ⟨index, boundRight⟩ := getAppendRight second index boundRight tail _

/-- `List.get` commutes with `List.map`, propext-free by induction on the list. -/
theorem getMap {Source Target : Type} (mapper : Source → Target) :
    (source : List Source) → (index : Nat) → (boundSource : index < source.length) →
    (boundMapped : index < (source.map mapper).length) →
    (source.map mapper).get ⟨index, boundMapped⟩ = mapper (source.get ⟨index, boundSource⟩)
  | _ :: _, 0, _, _ => rfl
  | head :: tail, Nat.succ innerIndex, boundSource, boundMapped => by
      show (tail.map mapper).get ⟨innerIndex, _⟩ = mapper (tail.get ⟨innerIndex, _⟩)
      exact getMap mapper tail innerIndex
        (Nat.lt_of_succ_lt_succ boundSource) (Nat.lt_of_succ_lt_succ boundMapped)

/-! ## The shared-mode transport -/

/-- Transport a mode index across the shared-mode-count equality `source = target`.  Preserves `.val`
DEFINITIONALLY (so it computes and round-trips), and the bound moves via `rw` on a `Nat` `<` goal — propext-free
(a `▸` on the `.val` itself would pull `propext` per the codebase's cast discipline). -/
def castFinAcrossCount {source target : Nat} (sameCount : source = target)
    (index : Fin target) : Fin source :=
  ⟨index.val, by rw [sameCount]; exact index.isLt⟩

/-- The transport preserves `.val` on the nose. -/
theorem castFinAcrossCount_val {source target : Nat} (sameCount : source = target)
    (index : Fin target) : (castFinAcrossCount sameCount index).val = index.val := rfl

/-- The two transports (forward / backward) round-trip to the identity (both preserve `.val`). -/
theorem castFinAcrossCount_roundTrip {smaller larger : Nat} (sameCount : smaller = larger)
    (index : Fin smaller) :
    castFinAcrossCount sameCount (castFinAcrossCount sameCount.symm index) = index :=
  Fin.ext rfl

/-! ## The tagged 1-generator sum -/

/-- The **combined 1-generator list** — `comp1`'s generators, then `comp2`'s generators with their endpoints
retagged across the shared-mode-count equality.  The tag is the index range: a component-1 generator has index
`< comp1.modalityGenerators.length`; a component-2 generator has index `≥ comp1.modalityGenerators.length`. -/
def combinedModalityGenerators (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) :
    List (Fin comp1.modeCount × Fin comp1.modeCount) :=
  comp1.modalityGenerators
    ++ comp2.modalityGenerators.map
        (fun endpoints => (castFinAcrossCount sameModes endpoints.1, castFinAcrossCount sameModes endpoints.2))

/-- The combined generator count is `len1 + len2` — the free-product / coproduct dimension count. -/
theorem combinedModalityGenerators_length (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) :
    (combinedModalityGenerators comp1 comp2 sameModes).length
      = comp1.modalityGenerators.length + comp2.modalityGenerators.length := by
  show (comp1.modalityGenerators ++ _).length = _
  rw [lengthAppend, lengthMap]

/-- Embed a component-1 generator index into the combined list (index unchanged, `< len1`). -/
def embedLeftLetter (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp1.modalityGenerators.length) :
    Fin (combinedModalityGenerators comp1 comp2 sameModes).length :=
  ⟨index.val, by
    rw [combinedModalityGenerators_length]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩

/-- Embed a component-2 generator index into the combined list (index shifted by `len1`). -/
def embedRightLetter (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp2.modalityGenerators.length) :
    Fin (combinedModalityGenerators comp1 comp2 sameModes).length :=
  ⟨comp1.modalityGenerators.length + index.val, by
    rw [combinedModalityGenerators_length]
    exact Nat.add_lt_add_left index.isLt _⟩

/-! ## The relation retag -/

/-- Retag a component-1 2-generator into the combined computad — endpoints unchanged (shared modes), letters
embedded into the left index range. -/
def retagLeftTwoGen (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (generator : ComputadTwoGen comp1.modeCount comp1.modalityGenerators) :
    ComputadTwoGen comp1.modeCount (combinedModalityGenerators comp1 comp2 sameModes) where
  src := generator.src
  tgt := generator.tgt
  lhs := generator.lhs.map (embedLeftLetter comp1 comp2 sameModes)
  rhs := generator.rhs.map (embedLeftLetter comp1 comp2 sameModes)

/-- Retag a component-2 2-generator into the combined computad — endpoints transported across the shared-mode
equality, letters embedded into the right index range. -/
def retagRightTwoGen (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (generator : ComputadTwoGen comp2.modeCount comp2.modalityGenerators) :
    ComputadTwoGen comp1.modeCount (combinedModalityGenerators comp1 comp2 sameModes) where
  src := castFinAcrossCount sameModes generator.src
  tgt := castFinAcrossCount sameModes generator.tgt
  lhs := generator.lhs.map (embedRightLetter comp1 comp2 sameModes)
  rhs := generator.rhs.map (embedRightLetter comp1 comp2 sameModes)

/-! ## The pushout -/

/-- ★ The **mode-signature pushout over a shared mode set** — `comp1 +_M comp2`: the shared mode count, the
tagged 1-generator sum, and the union of relations (each 2-generator retagged to its component's letter range).
A total, zero-axiom constructor `ModeComputad → ModeComputad → ModeComputad`. -/
def pushoutShared (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount) :
    ModeComputad where
  modeCount := comp1.modeCount
  modalityGenerators := combinedModalityGenerators comp1 comp2 sameModes
  twoCellGenerators :=
    comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)
      ++ comp2.twoCellGenerators.map (retagRightTwoGen comp1 comp2 sameModes)

/-- The pushout keeps the shared mode count. -/
theorem pushoutShared_modeCount (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) :
    (pushoutShared comp1 comp2 sameModes).modeCount = comp1.modeCount := rfl

/-- The pushout's 1-generators ARE the tagged generator sum. -/
theorem pushoutShared_modalityGenerators (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) :
    (pushoutShared comp1 comp2 sameModes).modalityGenerators
      = combinedModalityGenerators comp1 comp2 sameModes := rfl

/-- The pushout's relation count is the sum of the components' relation counts (disjoint union of relations). -/
theorem pushoutShared_twoCellCount (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) :
    (pushoutShared comp1 comp2 sameModes).twoCellGenerators.length
      = comp1.twoCellGenerators.length + comp2.twoCellGenerators.length := by
  show (comp1.twoCellGenerators.map _ ++ comp2.twoCellGenerators.map _).length = _
  rw [lengthAppend, lengthMap, lengthMap]

/-! ## Component tagging + projection -/

/-- The **component tag** of a combined 1-generator — `true` for component 1 (index `< len1`), `false` for
component 2.  A pure `Bool` (`Nat.blt`), so it computes under `#eval` / `decide`. -/
def combinedGeneratorComponent (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (generator : Fin (combinedModalityGenerators comp1 comp2 sameModes).length) : Bool :=
  Nat.blt generator.val comp1.modalityGenerators.length

/-- The component-1 embedding lands in component 1 (tag `true`). -/
theorem embedLeftLetter_component (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) (index : Fin comp1.modalityGenerators.length) :
    combinedGeneratorComponent comp1 comp2 sameModes (embedLeftLetter comp1 comp2 sameModes index) = true :=
  bltTrueOfLt index.isLt

/-- The component-2 embedding lands in component 2 (tag `false`). -/
theorem embedRightLetter_component (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) (index : Fin comp2.modalityGenerators.length) :
    combinedGeneratorComponent comp1 comp2 sameModes (embedRightLetter comp1 comp2 sameModes index) = false :=
  bltFalseOfGe (Nat.le_add_right comp1.modalityGenerators.length index.val)

/-! ## Computad morphisms + the coprojections -/

/-- A **computad morphism** — a signature morphism: a mode map and a 1-generator map that PRESERVES endpoints
(the generator's recorded `(src, tgt)` is carried by the mode map).  The right notion of a map of finite
2-computad presentations at the 0/1-skeleton level. -/
structure ComputadMorphism (source target : ModeComputad) where
  /-- The action on modes (0-cells). -/
  onModes : Fin source.modeCount → Fin target.modeCount
  /-- The action on 1-generators. -/
  onModalityGenerators : Fin source.modalityGenerators.length → Fin target.modalityGenerators.length
  /-- Endpoint preservation — the image generator's endpoints are the mode-map images of the source
  generator's endpoints. -/
  endpointsPreserved : ∀ (generatorIndex : Fin source.modalityGenerators.length),
    target.modalityGenerators.get (onModalityGenerators generatorIndex)
      = (onModes (source.modalityGenerators.get generatorIndex).1,
         onModes (source.modalityGenerators.get generatorIndex).2)

/-- ★ The **left coprojection** `comp1 → comp1 +_M comp2` — identity on modes, the left index embedding on
generators, endpoint preservation by `getAppendLeft`. -/
def inclusionLeft (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount) :
    ComputadMorphism comp1 (pushoutShared comp1 comp2 sameModes) where
  onModes := fun mode => mode
  onModalityGenerators := embedLeftLetter comp1 comp2 sameModes
  endpointsPreserved := fun generatorIndex => by
    show (combinedModalityGenerators comp1 comp2 sameModes).get
          (embedLeftLetter comp1 comp2 sameModes generatorIndex) = _
    exact getAppendLeft comp1.modalityGenerators _ generatorIndex.val generatorIndex.isLt _

/-- ★ The **right coprojection** `comp2 → comp1 +_M comp2` — the shared-mode transport on modes, the right index
embedding on generators, endpoint preservation by `getAppendRight` + `getMap`. -/
def inclusionRight (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount) :
    ComputadMorphism comp2 (pushoutShared comp1 comp2 sameModes) where
  onModes := castFinAcrossCount sameModes
  onModalityGenerators := embedRightLetter comp1 comp2 sameModes
  endpointsPreserved := fun generatorIndex => by
    show (combinedModalityGenerators comp1 comp2 sameModes).get
          ⟨comp1.modalityGenerators.length + generatorIndex.val, _⟩ = _
    have boundMapped : generatorIndex.val
        < (comp2.modalityGenerators.map
            (fun endpoints => (castFinAcrossCount sameModes endpoints.1,
              castFinAcrossCount sameModes endpoints.2))).length := by
      rw [lengthMap]; exact generatorIndex.isLt
    calc (combinedModalityGenerators comp1 comp2 sameModes).get
              ⟨comp1.modalityGenerators.length + generatorIndex.val, _⟩
        = (comp2.modalityGenerators.map
            (fun endpoints => (castFinAcrossCount sameModes endpoints.1,
              castFinAcrossCount sameModes endpoints.2))).get ⟨generatorIndex.val, boundMapped⟩ :=
            getAppendRight _ generatorIndex.val boundMapped comp1.modalityGenerators _
      _ = (castFinAcrossCount sameModes (comp2.modalityGenerators.get generatorIndex).1,
            castFinAcrossCount sameModes (comp2.modalityGenerators.get generatorIndex).2) :=
            getMap _ comp2.modalityGenerators generatorIndex.val generatorIndex.isLt boundMapped

/-! ## The copairing — the easy direction of the universal property -/

/-- The **copairing map** on 1-generators — route a combined generator to `f1` when it is component-1 (index
`< len1`), to `f2` (shifting the index down by `len1`) when it is component-2.  `dite` on `Nat.decLt`
(propext-free). -/
def copairOnGenerators (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (generator : Fin (combinedModalityGenerators comp1 comp2 sameModes).length) :
    Fin target.modalityGenerators.length :=
  if isComponentOne : generator.val < comp1.modalityGenerators.length then
    mapLeft.onModalityGenerators ⟨generator.val, isComponentOne⟩
  else
    mapRight.onModalityGenerators
      ⟨generator.val - comp1.modalityGenerators.length, by
        have belowSum : generator.val < comp1.modalityGenerators.length + comp2.modalityGenerators.length := by
          rw [← combinedModalityGenerators_length]; exact generator.isLt
        exact subLtOfLtAdd (Nat.le_of_not_lt isComponentOne) belowSum⟩

/-- The copairing routes the LEFT embedding back through `mapLeft` on generators — the left restriction, on the
underlying generator map. -/
theorem copairOnGenerators_left (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (index : Fin comp1.modalityGenerators.length) :
    copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight
        (embedLeftLetter comp1 comp2 sameModes index)
      = mapLeft.onModalityGenerators index := by
  show (if isComponentOne : index.val < comp1.modalityGenerators.length then
          mapLeft.onModalityGenerators ⟨index.val, isComponentOne⟩ else _) = _
  rw [dif_pos index.isLt]

/-- The copairing routes the RIGHT embedding back through `mapRight` on generators — the right restriction, on
the underlying generator map. -/
theorem copairOnGenerators_right (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (index : Fin comp2.modalityGenerators.length) :
    copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight
        (embedRightLetter comp1 comp2 sameModes index)
      = mapRight.onModalityGenerators index := by
  have notComponentOne : ¬ comp1.modalityGenerators.length + index.val < comp1.modalityGenerators.length :=
    fun bad => Nat.not_succ_le_self _ (Nat.le_trans bad (Nat.le_add_right _ _))
  show (if isComponentOne : comp1.modalityGenerators.length + index.val < comp1.modalityGenerators.length then _
        else mapRight.onModalityGenerators ⟨(comp1.modalityGenerators.length + index.val)
              - comp1.modalityGenerators.length, _⟩) = _
  rw [dif_neg notComponentOne]
  exact congrArg mapRight.onModalityGenerators
    (Fin.ext (addSubCancelLeft comp1.modalityGenerators.length index.val))

/-- ★ **The copairing — easy direction of the universal property.**  Given two morphisms out of the components
that AGREE on the shared modes (`mapLeft.onModes = mapRight.onModes ∘ (shared-mode transport)`), the copairing
is a morphism out of the pushout that restricts to each.  Its restrictions along the coprojections recover the
underlying generator maps (`copairMorphism_restrictsLeft` / `_restrictsRight`).  The endpoint-preservation field
is proven from the components' preservation plus the mode agreement. -/
def copairMorphism (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (modesAgree : ∀ (mode : Fin comp2.modeCount),
      mapLeft.onModes (castFinAcrossCount sameModes mode) = mapRight.onModes mode) :
    ComputadMorphism (pushoutShared comp1 comp2 sameModes) target where
  onModes := mapLeft.onModes
  onModalityGenerators := copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight
  endpointsPreserved := fun generatorIndex => by
    show target.modalityGenerators.get
          (copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight generatorIndex) = _
    by_cases isComponentOne : generatorIndex.val < comp1.modalityGenerators.length
    · -- component 1: route through mapLeft, source generator is the left append part
      rw [show copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight generatorIndex
            = mapLeft.onModalityGenerators ⟨generatorIndex.val, isComponentOne⟩ from by
          show (if h : generatorIndex.val < comp1.modalityGenerators.length then
                  mapLeft.onModalityGenerators ⟨generatorIndex.val, h⟩ else _) = _
          rw [dif_pos isComponentOne]]
      rw [mapLeft.endpointsPreserved ⟨generatorIndex.val, isComponentOne⟩]
      have sourceEq : (combinedModalityGenerators comp1 comp2 sameModes).get generatorIndex
          = comp1.modalityGenerators.get ⟨generatorIndex.val, isComponentOne⟩ := by
        show (comp1.modalityGenerators ++ _).get ⟨generatorIndex.val, _⟩ = _
        exact getAppendLeft comp1.modalityGenerators _ generatorIndex.val isComponentOne _
      rw [show (pushoutShared comp1 comp2 sameModes).modalityGenerators.get generatorIndex
            = (combinedModalityGenerators comp1 comp2 sameModes).get generatorIndex from rfl, sourceEq]
    · -- component 2: route through mapRight, source generator is the retagged right append part
      have geLeft : comp1.modalityGenerators.length ≤ generatorIndex.val := Nat.le_of_not_lt isComponentOne
      have downIndexLt : generatorIndex.val - comp1.modalityGenerators.length
          < comp2.modalityGenerators.length := by
        have belowSum : generatorIndex.val
            < comp1.modalityGenerators.length + comp2.modalityGenerators.length := by
          rw [← combinedModalityGenerators_length]; exact generatorIndex.isLt
        exact subLtOfLtAdd geLeft belowSum
      rw [show copairOnGenerators comp1 comp2 target sameModes mapLeft mapRight generatorIndex
            = mapRight.onModalityGenerators
                ⟨generatorIndex.val - comp1.modalityGenerators.length, downIndexLt⟩ from by
          show (if h : generatorIndex.val < comp1.modalityGenerators.length then _
                else mapRight.onModalityGenerators ⟨generatorIndex.val - comp1.modalityGenerators.length, _⟩) = _
          rw [dif_neg isComponentOne]]
      rw [mapRight.endpointsPreserved ⟨generatorIndex.val - comp1.modalityGenerators.length, downIndexLt⟩]
      -- reconstruct the combined generator as the retagged right part
      have boundMapped : generatorIndex.val - comp1.modalityGenerators.length
          < (comp2.modalityGenerators.map
              (fun endpoints => (castFinAcrossCount sameModes endpoints.1,
                castFinAcrossCount sameModes endpoints.2))).length := by
        rw [lengthMap]; exact downIndexLt
      have valBack : comp1.modalityGenerators.length
          + (generatorIndex.val - comp1.modalityGenerators.length) = generatorIndex.val :=
        addSubCancel geLeft
      have sourceEq : (combinedModalityGenerators comp1 comp2 sameModes).get generatorIndex
          = (castFinAcrossCount sameModes
                (comp2.modalityGenerators.get
                  ⟨generatorIndex.val - comp1.modalityGenerators.length, downIndexLt⟩).1,
             castFinAcrossCount sameModes
                (comp2.modalityGenerators.get
                  ⟨generatorIndex.val - comp1.modalityGenerators.length, downIndexLt⟩).2) := by
        have step : (combinedModalityGenerators comp1 comp2 sameModes).get
              ⟨comp1.modalityGenerators.length
                + (generatorIndex.val - comp1.modalityGenerators.length), by rw [valBack]; exact generatorIndex.isLt⟩
            = (comp2.modalityGenerators.map
                (fun endpoints => (castFinAcrossCount sameModes endpoints.1,
                  castFinAcrossCount sameModes endpoints.2))).get
                ⟨generatorIndex.val - comp1.modalityGenerators.length, boundMapped⟩ := by
          show (comp1.modalityGenerators ++ _).get
                ⟨comp1.modalityGenerators.length + _, _⟩ = _
          exact getAppendRight _ (generatorIndex.val - comp1.modalityGenerators.length) boundMapped
            comp1.modalityGenerators _
        rw [getMap _ comp2.modalityGenerators (generatorIndex.val - comp1.modalityGenerators.length)
              downIndexLt boundMapped] at step
        rw [← step]
        exact getValCongr (combinedModalityGenerators comp1 comp2 sameModes) valBack.symm
      rw [show (pushoutShared comp1 comp2 sameModes).modalityGenerators.get generatorIndex
            = (combinedModalityGenerators comp1 comp2 sameModes).get generatorIndex from rfl, sourceEq]
      -- push mapRight.onModes through the shared-mode transport using modesAgree
      exact congrArg (fun modePair : Fin target.modeCount × Fin target.modeCount => modePair)
        (by rw [modesAgree, modesAgree])

/-- The copairing restricts to `mapLeft` along the left coprojection (underlying generator map). -/
theorem copairMorphism_restrictsLeft (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (modesAgree : ∀ (mode : Fin comp2.modeCount),
      mapLeft.onModes (castFinAcrossCount sameModes mode) = mapRight.onModes mode)
    (index : Fin comp1.modalityGenerators.length) :
    (copairMorphism comp1 comp2 target sameModes mapLeft mapRight modesAgree).onModalityGenerators
        ((inclusionLeft comp1 comp2 sameModes).onModalityGenerators index)
      = mapLeft.onModalityGenerators index :=
  copairOnGenerators_left comp1 comp2 target sameModes mapLeft mapRight index

/-- The copairing restricts to `mapRight` along the right coprojection (underlying generator map). -/
theorem copairMorphism_restrictsRight (comp1 comp2 target : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (mapLeft : ComputadMorphism comp1 target) (mapRight : ComputadMorphism comp2 target)
    (modesAgree : ∀ (mode : Fin comp2.modeCount),
      mapLeft.onModes (castFinAcrossCount sameModes mode) = mapRight.onModes mode)
    (index : Fin comp2.modalityGenerators.length) :
    (copairMorphism comp1 comp2 target sameModes mapLeft mapRight modesAgree).onModalityGenerators
        ((inclusionRight comp1 comp2 sameModes).onModalityGenerators index)
      = mapRight.onModalityGenerators index :=
  copairOnGenerators_right comp1 comp2 target sameModes mapLeft mapRight index

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the mode-signature pushout over a shared mode set SHIPS.**  The tagged 1-generator sum
(`combinedModalityGenerators`, with the `len1 + len2` dimension count), the pushout computad (`pushoutShared`,
shape smokes proven), component tagging (`combinedGeneratorComponent`, computes), the two coprojections
(`inclusionLeft` / `inclusionRight`, full endpoint-preserving `ComputadMorphism`s), and the EASY direction of
the universal property (`copairMorphism` with `copairMorphism_restrictsLeft` / `_restrictsRight`).  Governing
prior art: the disjoint-signature word-problem combination (Pigozzi 1974 / Baader-Tinelli 1998).  `= true`. -/
def fxAmalg_hasSignaturePushout : Bool := true

/-- **Honesty marker.**  The UNIQUENESS / full factoring half of the universal property (every morphism out of
the pushout is the copairing of its restrictions) is the hard direction, deferred.  `= false`. -/
def fxAmalg_hasSignaturePushoutUniqueness : Bool := false

end FX1Poly.Polygraph.Amalgam
