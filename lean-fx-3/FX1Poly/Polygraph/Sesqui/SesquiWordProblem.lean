/-! # Sesquicategory / premonoidal word problem — ordered-whisker normal form

A **sesquicategory** (Street) is "a category enriched in `Cat` WITHOUT the
interchange law" — equivalently a strict 2-category minus the Godement
middle-four exchange, equivalently the algebraic skeleton of a premonoidal
category (Power–Robinson).  It has objects, 1-cells (composable), 2-cells with
vertical composition, and left/right whiskering of a 2-cell by a 1-cell — and
these whiskerings are *functorial* (whisker of a vertical composite is the
vertical composite of whiskers, whisker of an identity is an identity) and
*action-compatible* (whiskering along a composite 1-cell factors, whiskering by
the identity 1-cell is a no-op, left- and right-whiskering commute).  The one
law it does NOT have is interchange:

  `(alpha |> d) ; (c' <| beta)  =  (c <| beta) ; (alpha |> d)`

WITHOUT interchange the horizontal order of disjoint-support whiskerings is
rigid; the normal form here is an **ordered frame list** and two 2-cells that
differ only by a would-be interchange swap are DISTINCT.

This file gives a fully self-contained, zero-axiom word problem for the free
sesquicategory on a single (mode-forgetful) polygraph:

* 1-cells        = a hand-rolled cons-only list of generator indices
                   (`OneCell`), with own `append`, own structural `beq`, and a
                   `beq → eq` soundness proof (no `List.beq` leaky lemmas).
* 2-cell frame   = `(leftContext, genIndex, rightContext)` — a single
                   whiskered generator `leftContext <| gen |> rightContext`.
* 2-cell term    = `TwoCell` with `id / gen / vcomp / whiskerLeft / whiskerRight`.
* normal form    = `normalize : TwoCell → FrameList`, an ordered list of frames,
                   applying whisker-functoriality but NOT interchange.
* decision       = `decideSesquiEq l r := FrameList.beq (normalize l) (normalize r)`.
* congruence     = `SesquiConv` (the eleven sesqui laws, interchange EXCLUDED),
                   proven SOUND and COMPLETE against `normalize`.

The interchange / premonoidal-centre wall is stated at the end.

Zero-axiom: everything is structural recursion over cons-only lists with own
`append` (Init's `List.append`/`++` route through `propext`, so we hand-roll),
own boolean `beq` via full-enumeration / nested `match` (no `&&`, no `Bool`
lemmas), and `congrArg` / structure-eta for the frame algebra. -/

namespace FX1Poly.Polygraph.Sesqui

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1-cells: a cons-only word of generator indices -/

/-- A 1-cell is a word over the 1-generator alphabet (generator indices),
represented as a hand-rolled cons list so that composition (`append`) and
equality (`beq`) never touch `propext`-leaking `List` lemmas. -/
inductive OneCell where
  | nil
  | cons (head : Nat) (tail : OneCell)

/-- 1-cell composition: word concatenation, cons-only (own `append`). -/
def OneCell.append : OneCell → OneCell → OneCell
  | .nil, ys => ys
  | .cons head tail, ys => .cons head (OneCell.append tail ys)

/-- Right identity of 1-cell composition: `w . id = w`. -/
theorem OneCell.append_nil : ∀ word : OneCell, OneCell.append word OneCell.nil = word
  | .nil => rfl
  | .cons head tail => congrArg (OneCell.cons head) (OneCell.append_nil tail)

/-- Associativity of 1-cell composition. -/
theorem OneCell.append_assoc :
    ∀ first second third : OneCell,
      OneCell.append (OneCell.append first second) third
        = OneCell.append first (OneCell.append second third)
  | .nil, _, _ => rfl
  | .cons head tail, second, third =>
      congrArg (OneCell.cons head) (OneCell.append_assoc tail second third)

/-- Structural boolean equality on 1-cells, via nested `match` on `Nat.beq`
(no `&&`, so no `Bool`-lemma propext leak). -/
def OneCell.beq : OneCell → OneCell → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons head1 tail1, .cons head2 tail2 =>
      match Nat.beq head1 head2 with
      | false => false
      | true => OneCell.beq tail1 tail2

/-- Own `Nat.beq` reflexivity, hand-rolled structurally (Init's `Nat.beq_refl`
routes through `propext`). -/
theorem natBeqSelf : ∀ value : Nat, Nat.beq value value = true
  | 0 => rfl
  | .succ inner => natBeqSelf inner

/-- `beq` is reflexive on 1-cells. -/
theorem OneCell.beq_refl : ∀ word : OneCell, OneCell.beq word word = true
  | .nil => rfl
  | .cons head tail => by
      show (match Nat.beq head head with
            | false => false
            | true => OneCell.beq tail tail) = true
      cases hmatch : Nat.beq head head with
      | false => exact Bool.noConfusion ((natBeqSelf head).symm.trans hmatch)
      | true => exact OneCell.beq_refl tail

/-- Soundness of 1-cell `beq`: `beq = true → eq`. -/
theorem OneCell.eq_of_beq :
    ∀ first second : OneCell, OneCell.beq first second = true → first = second
  | .nil, .nil, _ => rfl
  | .cons head1 tail1, .cons head2 tail2, hbeq => by
      show (.cons head1 tail1 : OneCell) = .cons head2 tail2
      have hmatch : (match Nat.beq head1 head2 with
                     | false => false
                     | true => OneCell.beq tail1 tail2) = true := hbeq
      cases hnat : Nat.beq head1 head2 with
      | false => rw [hnat] at hmatch; exact Bool.noConfusion hmatch
      | true =>
          rw [hnat] at hmatch
          have hhead : head1 = head2 := Nat.eq_of_beq_eq_true hnat
          have htail : tail1 = tail2 := OneCell.eq_of_beq tail1 tail2 hmatch
          rw [hhead, htail]

/-! ## 2-cell frames and the ordered-frame carrier -/

/-- A single whiskered generator 2-cell: `leftContext <| gen(genIndex) |> rightContext`.
This is exactly the rigid frame `(leftContext, genIndex, rightContext)`. -/
structure Frame where
  leftContext : OneCell
  genIndex : Nat
  rightContext : OneCell

/-- The ordered frame list — a vertical composite of whiskered generators.
This is the sesquicategory normal form: interchange would permute
disjoint-support frames, this rigid list does NOT. -/
inductive FrameList where
  | nil
  | cons (head : Frame) (tail : FrameList)

/-- Vertical composition of normal forms: frame-list concatenation. -/
def FrameList.append : FrameList → FrameList → FrameList
  | .nil, ys => ys
  | .cons head tail, ys => .cons head (FrameList.append tail ys)

/-- Right identity of vertical composition on normal forms. -/
theorem FrameList.append_nil :
    ∀ frames : FrameList, FrameList.append frames FrameList.nil = frames
  | .nil => rfl
  | .cons head tail => congrArg (FrameList.cons head) (FrameList.append_nil tail)

/-- Associativity of vertical composition on normal forms. -/
theorem FrameList.append_assoc :
    ∀ first second third : FrameList,
      FrameList.append (FrameList.append first second) third
        = FrameList.append first (FrameList.append second third)
  | .nil, _, _ => rfl
  | .cons head tail, second, third =>
      congrArg (FrameList.cons head) (FrameList.append_assoc tail second third)

/-- Structural boolean equality on frames (nested `match`, no `&&`). -/
def Frame.beq : Frame → Frame → Bool
  | ⟨left1, index1, right1⟩, ⟨left2, index2, right2⟩ =>
      match Nat.beq index1 index2 with
      | false => false
      | true =>
          match OneCell.beq left1 left2 with
          | false => false
          | true => OneCell.beq right1 right2

/-- `Frame.beq` is reflexive. -/
theorem Frame.beq_refl : ∀ frame : Frame, Frame.beq frame frame = true
  | ⟨left, index, right⟩ => by
      show (match Nat.beq index index with
            | false => false
            | true =>
                match OneCell.beq left left with
                | false => false
                | true => OneCell.beq right right) = true
      cases hindex : Nat.beq index index with
      | false => exact Bool.noConfusion ((natBeqSelf index).symm.trans hindex)
      | true =>
          cases hleft : OneCell.beq left left with
          | false => exact Bool.noConfusion ((OneCell.beq_refl left).symm.trans hleft)
          | true => exact OneCell.beq_refl right

/-- Soundness of `Frame.beq`. -/
theorem Frame.eq_of_beq :
    ∀ first second : Frame, Frame.beq first second = true → first = second
  | ⟨left1, index1, right1⟩, ⟨left2, index2, right2⟩, hbeq => by
      have hmatch : (match Nat.beq index1 index2 with
                     | false => false
                     | true =>
                         match OneCell.beq left1 left2 with
                         | false => false
                         | true => OneCell.beq right1 right2) = true := hbeq
      cases hindex : Nat.beq index1 index2 with
      | false => rw [hindex] at hmatch; exact Bool.noConfusion hmatch
      | true =>
          rw [hindex] at hmatch
          cases hleft : OneCell.beq left1 left2 with
          | false => rw [hleft] at hmatch; exact Bool.noConfusion hmatch
          | true =>
              rw [hleft] at hmatch
              have heqIndex : index1 = index2 := Nat.eq_of_beq_eq_true hindex
              have heqLeft : left1 = left2 := OneCell.eq_of_beq left1 left2 hleft
              have heqRight : right1 = right2 := OneCell.eq_of_beq right1 right2 hmatch
              rw [heqIndex, heqLeft, heqRight]

/-- Structural boolean equality on frame lists (nested `match`, no `&&`). -/
def FrameList.beq : FrameList → FrameList → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons head1 tail1, .cons head2 tail2 =>
      match Frame.beq head1 head2 with
      | false => false
      | true => FrameList.beq tail1 tail2

/-- `FrameList.beq` is reflexive. -/
theorem FrameList.beq_refl : ∀ frames : FrameList, FrameList.beq frames frames = true
  | .nil => rfl
  | .cons head tail => by
      show (match Frame.beq head head with
            | false => false
            | true => FrameList.beq tail tail) = true
      cases hmatch : Frame.beq head head with
      | false => exact Bool.noConfusion ((Frame.beq_refl head).symm.trans hmatch)
      | true => exact FrameList.beq_refl tail

/-- Soundness of `FrameList.beq`: `beq = true → eq`. -/
theorem FrameList.eq_of_beq :
    ∀ first second : FrameList, FrameList.beq first second = true → first = second
  | .nil, .nil, _ => rfl
  | .cons head1 tail1, .cons head2 tail2, hbeq => by
      show (.cons head1 tail1 : FrameList) = .cons head2 tail2
      have hmatch : (match Frame.beq head1 head2 with
                     | false => false
                     | true => FrameList.beq tail1 tail2) = true := hbeq
      cases hframe : Frame.beq head1 head2 with
      | false => rw [hframe] at hmatch; exact Bool.noConfusion hmatch
      | true =>
          rw [hframe] at hmatch
          have hhead : head1 = head2 := Frame.eq_of_beq head1 head2 hframe
          have htail : tail1 = tail2 := FrameList.eq_of_beq tail1 tail2 hmatch
          rw [hhead, htail]

/-! ## The whisker action on frames (prepend to left / append to right) -/

/-- Left-whisker a single frame by a 1-cell: prepend to the left context. -/
def whiskerLeftFrame (word : OneCell) (frame : Frame) : Frame :=
  ⟨OneCell.append word frame.leftContext, frame.genIndex, frame.rightContext⟩

/-- Right-whisker a single frame by a 1-cell: append to the right context. -/
def whiskerRightFrame (frame : Frame) (word : OneCell) : Frame :=
  ⟨frame.leftContext, frame.genIndex, OneCell.append frame.rightContext word⟩

/-- Left-whisker a whole frame list. -/
def whiskerLeftFrames (word : OneCell) : FrameList → FrameList
  | .nil => .nil
  | .cons head tail => .cons (whiskerLeftFrame word head) (whiskerLeftFrames word tail)

/-- Right-whisker a whole frame list. -/
def whiskerRightFrames : FrameList → OneCell → FrameList
  | .nil, _ => .nil
  | .cons head tail, word => .cons (whiskerRightFrame head word) (whiskerRightFrames tail word)

/-- Left-whiskering distributes over vertical composition (frame-list append):
this is left-whisker *functoriality on vcomp*. -/
theorem whiskerLeftFrames_append :
    ∀ (word : OneCell) (first second : FrameList),
      whiskerLeftFrames word (FrameList.append first second)
        = FrameList.append (whiskerLeftFrames word first) (whiskerLeftFrames word second)
  | _, .nil, _ => rfl
  | word, .cons head tail, second =>
      congrArg (FrameList.cons (whiskerLeftFrame word head))
        (whiskerLeftFrames_append word tail second)

/-- Right-whiskering distributes over vertical composition. -/
theorem whiskerRightFrames_append :
    ∀ (first second : FrameList) (word : OneCell),
      whiskerRightFrames (FrameList.append first second) word
        = FrameList.append (whiskerRightFrames first word) (whiskerRightFrames second word)
  | .nil, _, _ => rfl
  | .cons head tail, second, word =>
      congrArg (FrameList.cons (whiskerRightFrame head word))
        (whiskerRightFrames_append tail second word)

/-- Left-whisker along a composite 1-cell factors, per frame (needs `append_assoc`). -/
theorem whiskerLeftFrame_append :
    ∀ (first second : OneCell) (frame : Frame),
      whiskerLeftFrame (OneCell.append first second) frame
        = whiskerLeftFrame first (whiskerLeftFrame second frame)
  | first, second, ⟨left, index, right⟩ =>
      congrArg (fun composedLeft => (⟨composedLeft, index, right⟩ : Frame))
        (OneCell.append_assoc first second left)

/-- Left-whisker along a composite 1-cell factors, whole list. -/
theorem whiskerLeftFrames_composite :
    ∀ (first second : OneCell) (frames : FrameList),
      whiskerLeftFrames (OneCell.append first second) frames
        = whiskerLeftFrames first (whiskerLeftFrames second frames)
  | _, _, .nil => rfl
  | first, second, .cons head tail => by
      show (.cons (whiskerLeftFrame (OneCell.append first second) head)
             (whiskerLeftFrames (OneCell.append first second) tail) : FrameList)
           = .cons (whiskerLeftFrame first (whiskerLeftFrame second head))
             (whiskerLeftFrames first (whiskerLeftFrames second tail))
      rw [whiskerLeftFrame_append first second head,
          whiskerLeftFrames_composite first second tail]

/-- Right-whisker along a composite 1-cell factors, per frame. -/
theorem whiskerRightFrame_append :
    ∀ (frame : Frame) (first second : OneCell),
      whiskerRightFrame frame (OneCell.append first second)
        = whiskerRightFrame (whiskerRightFrame frame first) second
  | ⟨left, index, right⟩, first, second =>
      congrArg (fun composedRight => (⟨left, index, composedRight⟩ : Frame))
        (Eq.symm (OneCell.append_assoc right first second))

/-- Right-whisker along a composite 1-cell factors, whole list. -/
theorem whiskerRightFrames_composite :
    ∀ (frames : FrameList) (first second : OneCell),
      whiskerRightFrames frames (OneCell.append first second)
        = whiskerRightFrames (whiskerRightFrames frames first) second
  | .nil, _, _ => rfl
  | .cons head tail, first, second => by
      show (.cons (whiskerRightFrame head (OneCell.append first second))
             (whiskerRightFrames tail (OneCell.append first second)) : FrameList)
           = .cons (whiskerRightFrame (whiskerRightFrame head first) second)
             (whiskerRightFrames (whiskerRightFrames tail first) second)
      rw [whiskerRightFrame_append head first second,
          whiskerRightFrames_composite tail first second]

/-- Left-whisker by the identity 1-cell is a no-op (per frame it is `rfl` by
`append nil` reduction plus structure eta). -/
theorem whiskerLeftFrames_nil :
    ∀ frames : FrameList, whiskerLeftFrames OneCell.nil frames = frames
  | .nil => rfl
  | .cons head tail => congrArg (FrameList.cons head) (whiskerLeftFrames_nil tail)

/-- Right-whisker by the identity 1-cell is a no-op (per frame needs `append_nil`). -/
theorem whiskerRightFrames_nil :
    ∀ frames : FrameList, whiskerRightFrames frames OneCell.nil = frames
  | .nil => rfl
  | .cons ⟨left, index, right⟩ tail => by
      show (.cons (whiskerRightFrame ⟨left, index, right⟩ OneCell.nil)
             (whiskerRightFrames tail OneCell.nil) : FrameList)
           = .cons ⟨left, index, right⟩ tail
      rw [whiskerRightFrames_nil tail]
      show (.cons (⟨left, index, OneCell.append right OneCell.nil⟩ : Frame) tail : FrameList)
           = .cons ⟨left, index, right⟩ tail
      rw [OneCell.append_nil right]

/-- Left- and right-whiskering commute on a single frame (this is `rfl`: left
touches `leftContext`, right touches `rightContext`, independently). -/
theorem whiskerFrame_commute :
    ∀ (leftWord rightWord : OneCell) (frame : Frame),
      whiskerRightFrame (whiskerLeftFrame leftWord frame) rightWord
        = whiskerLeftFrame leftWord (whiskerRightFrame frame rightWord)
  | _, _, ⟨_, _, _⟩ => rfl

/-- Left- and right-whiskering commute on a whole frame list — the
sesquicategory whisker-action compatibility law. -/
theorem whiskerFrames_commute :
    ∀ (leftWord rightWord : OneCell) (frames : FrameList),
      whiskerRightFrames (whiskerLeftFrames leftWord frames) rightWord
        = whiskerLeftFrames leftWord (whiskerRightFrames frames rightWord)
  | _, _, .nil => rfl
  | leftWord, rightWord, .cons head tail => by
      show (.cons (whiskerRightFrame (whiskerLeftFrame leftWord head) rightWord)
             (whiskerRightFrames (whiskerLeftFrames leftWord tail) rightWord) : FrameList)
           = .cons (whiskerLeftFrame leftWord (whiskerRightFrame head rightWord))
             (whiskerLeftFrames leftWord (whiskerRightFrames tail rightWord))
      rw [whiskerFrame_commute leftWord rightWord head,
          whiskerFrames_commute leftWord rightWord tail]

/-! ## The 2-cell term language and its ordered-frame normal form -/

/-- A raw sesquicategory 2-cell expression: identity, generator, vertical
composition, and left / right whiskering by a 1-cell.  Interchange is NOT a
constructor and NOT a normalization step — that is the whole point. -/
inductive TwoCell where
  | id
  | gen (index : Nat)
  | vcomp (first second : TwoCell)
  | whiskerLeft (word : OneCell) (body : TwoCell)
  | whiskerRight (body : TwoCell) (word : OneCell)

/-- The ordered-whisker normal form: apply whisker-functoriality (whisker of
vcomp = vcomp of whiskers, whisker of id = id) down to an ordered list of
rigid frames.  Interchange is never applied, so the horizontal order of
disjoint-support frames is preserved. -/
def normalize : TwoCell → FrameList
  | .id => .nil
  | .gen index => .cons ⟨OneCell.nil, index, OneCell.nil⟩ .nil
  | .vcomp first second => FrameList.append (normalize first) (normalize second)
  | .whiskerLeft word body => whiskerLeftFrames word (normalize body)
  | .whiskerRight body word => whiskerRightFrames (normalize body) word

/-- The decision procedure: normalize both sides and compare frame lists. -/
def decideSesquiEq (first second : TwoCell) : Bool :=
  FrameList.beq (normalize first) (normalize second)

/-! ## The sesquicategory congruence (interchange EXCLUDED) -/

/-- `SesquiConv` is the congruence generated by the eleven sesquicategory laws.
It is an equivalence relation, a congruence for `vcomp` / `whiskerLeft` /
`whiskerRight`, and closed under the generating laws below.  Crucially it does
NOT contain interchange. -/
inductive SesquiConv : TwoCell → TwoCell → Prop where
  | refl (cell : TwoCell) : SesquiConv cell cell
  | symm {first second : TwoCell} : SesquiConv first second → SesquiConv second first
  | trans {first second third : TwoCell} :
      SesquiConv first second → SesquiConv second third → SesquiConv first third
  | vcompCongr {first1 first2 second1 second2 : TwoCell} :
      SesquiConv first1 first2 → SesquiConv second1 second2 →
      SesquiConv (.vcomp first1 second1) (.vcomp first2 second2)
  | whiskerLeftCongr {word : OneCell} {body1 body2 : TwoCell} :
      SesquiConv body1 body2 → SesquiConv (.whiskerLeft word body1) (.whiskerLeft word body2)
  | whiskerRightCongr {word : OneCell} {body1 body2 : TwoCell} :
      SesquiConv body1 body2 → SesquiConv (.whiskerRight body1 word) (.whiskerRight body2 word)
  | vcompAssoc (first second third : TwoCell) :
      SesquiConv (.vcomp (.vcomp first second) third) (.vcomp first (.vcomp second third))
  | vcompIdLeft (cell : TwoCell) : SesquiConv (.vcomp .id cell) cell
  | vcompIdRight (cell : TwoCell) : SesquiConv (.vcomp cell .id) cell
  | whiskerLeftId (word : OneCell) : SesquiConv (.whiskerLeft word .id) .id
  | whiskerRightId (word : OneCell) : SesquiConv (.whiskerRight .id word) .id
  | whiskerLeftVcomp (word : OneCell) (first second : TwoCell) :
      SesquiConv (.whiskerLeft word (.vcomp first second))
        (.vcomp (.whiskerLeft word first) (.whiskerLeft word second))
  | whiskerRightVcomp (word : OneCell) (first second : TwoCell) :
      SesquiConv (.whiskerRight (.vcomp first second) word)
        (.vcomp (.whiskerRight first word) (.whiskerRight second word))
  | whiskerLeftComposite (first second : OneCell) (body : TwoCell) :
      SesquiConv (.whiskerLeft (OneCell.append first second) body)
        (.whiskerLeft first (.whiskerLeft second body))
  | whiskerRightComposite (body : TwoCell) (first second : OneCell) :
      SesquiConv (.whiskerRight body (OneCell.append first second))
        (.whiskerRight (.whiskerRight body first) second)
  | whiskerLeftNil (body : TwoCell) : SesquiConv (.whiskerLeft OneCell.nil body) body
  | whiskerRightNil (body : TwoCell) : SesquiConv (.whiskerRight body OneCell.nil) body
  | whiskerCommute (leftWord rightWord : OneCell) (body : TwoCell) :
      SesquiConv (.whiskerRight (.whiskerLeft leftWord body) rightWord)
        (.whiskerLeft leftWord (.whiskerRight body rightWord))

/-! ## T2 — whisker-functoriality soundness: `SesquiConv l r → normalize l = normalize r` -/

/-- Every sesquicategory law is a normal-form identity, and the congruence lifts. -/
theorem normalize_eq_of_sesquiConv :
    ∀ {first second : TwoCell}, SesquiConv first second → normalize first = normalize second
  | _, _, .refl _ => rfl
  | _, _, .symm conv => Eq.symm (normalize_eq_of_sesquiConv conv)
  | _, _, .trans conv1 conv2 =>
      Eq.trans (normalize_eq_of_sesquiConv conv1) (normalize_eq_of_sesquiConv conv2)
  | _, _, .vcompCongr conv1 conv2 => by
      show FrameList.append (normalize _) (normalize _)
             = FrameList.append (normalize _) (normalize _)
      rw [normalize_eq_of_sesquiConv conv1, normalize_eq_of_sesquiConv conv2]
  | _, _, .whiskerLeftCongr conv => by
      show whiskerLeftFrames _ (normalize _) = whiskerLeftFrames _ (normalize _)
      rw [normalize_eq_of_sesquiConv conv]
  | _, _, .whiskerRightCongr conv => by
      show whiskerRightFrames (normalize _) _ = whiskerRightFrames (normalize _) _
      rw [normalize_eq_of_sesquiConv conv]
  | _, _, .vcompAssoc first second third =>
      FrameList.append_assoc (normalize first) (normalize second) (normalize third)
  | _, _, .vcompIdLeft _ => rfl
  | _, _, .vcompIdRight cell => FrameList.append_nil (normalize cell)
  | _, _, .whiskerLeftId _ => rfl
  | _, _, .whiskerRightId _ => rfl
  | _, _, .whiskerLeftVcomp word first second =>
      whiskerLeftFrames_append word (normalize first) (normalize second)
  | _, _, .whiskerRightVcomp word first second =>
      whiskerRightFrames_append (normalize first) (normalize second) word
  | _, _, .whiskerLeftComposite first second body =>
      whiskerLeftFrames_composite first second (normalize body)
  | _, _, .whiskerRightComposite body first second =>
      whiskerRightFrames_composite (normalize body) first second
  | _, _, .whiskerLeftNil body => whiskerLeftFrames_nil (normalize body)
  | _, _, .whiskerRightNil body => whiskerRightFrames_nil (normalize body)
  | _, _, .whiskerCommute leftWord rightWord body =>
      whiskerFrames_commute leftWord rightWord (normalize body)

/-! ## T3 — the decision: soundness and refutation -/

/-- Soundness of the decision procedure: convertible 2-cells decide equal.
Written in pure `Eq` term mode (`congrArg` / `trans` / `symm`) to stay
`propext`-free — `rw` under `beq _ = true` routes through `propext`. -/
theorem decideSesquiEq_of_sesquiConv {first second : TwoCell} :
    SesquiConv first second → decideSesquiEq first second = true := fun conv =>
  Eq.trans
    (Eq.symm (congrArg (FrameList.beq (normalize first)) (normalize_eq_of_sesquiConv conv)))
    (FrameList.beq_refl (normalize first))

/-- Refutation half: if the decision returns `false`, the 2-cells are NOT
sesqui-convertible (distinct ordered-frame lists are not convertible). -/
theorem not_sesquiConv_of_decideSesquiEq_false {first second : TwoCell} :
    decideSesquiEq first second = false → ¬ SesquiConv first second := fun hfalse conv =>
  Bool.noConfusion (Eq.trans (Eq.symm (decideSesquiEq_of_sesquiConv conv)) hfalse)

/-! ## T3 completeness — every 2-cell is convertible to its ordered-frame normal form -/

/-- Reify one frame back to a canonical whiskered generator 2-cell. -/
def Frame.reify (frame : Frame) : TwoCell :=
  .whiskerRight (.whiskerLeft frame.leftContext (.gen frame.genIndex)) frame.rightContext

/-- Reify a normal form back to a canonical 2-cell term (right-nested vcomp). -/
def FrameList.reify : FrameList → TwoCell
  | .nil => .id
  | .cons head tail => .vcomp (Frame.reify head) (FrameList.reify tail)

/-- Reify of an appended normal form is convertible to the vcomp of reifications. -/
theorem sesquiConv_reify_append :
    ∀ first second : FrameList,
      SesquiConv (FrameList.reify (FrameList.append first second))
        (.vcomp (FrameList.reify first) (FrameList.reify second))
  | .nil, second =>
      -- reify (append nil second) = reify second; vcomp id (reify second) ~ reify second
      SesquiConv.symm (SesquiConv.vcompIdLeft (FrameList.reify second))
  | .cons head tail, second => by
      -- reify (cons head (append tail second))
      --   = vcomp (reify head) (reify (append tail second))
      -- target: vcomp (vcomp (reify head) (reify tail)) (reify second)
      show SesquiConv (.vcomp (Frame.reify head) (FrameList.reify (FrameList.append tail second)))
             (.vcomp (.vcomp (Frame.reify head) (FrameList.reify tail)) (FrameList.reify second))
      have hstep : SesquiConv (.vcomp (Frame.reify head) (FrameList.reify (FrameList.append tail second)))
          (.vcomp (Frame.reify head) (.vcomp (FrameList.reify tail) (FrameList.reify second))) :=
        SesquiConv.vcompCongr (SesquiConv.refl (Frame.reify head)) (sesquiConv_reify_append tail second)
      exact SesquiConv.trans hstep
        (SesquiConv.symm (SesquiConv.vcompAssoc (Frame.reify head) (FrameList.reify tail)
          (FrameList.reify second)))

/-- Reify commutes with left-whiskering, up to convertibility. -/
theorem sesquiConv_reify_whiskerLeft :
    ∀ (word : OneCell) (frames : FrameList),
      SesquiConv (FrameList.reify (whiskerLeftFrames word frames))
        (.whiskerLeft word (FrameList.reify frames))
  | word, .nil =>
      -- reify nil = id; whiskerLeft word id ~ id
      SesquiConv.symm (SesquiConv.whiskerLeftId word)
  | word, .cons head tail => by
      show SesquiConv (.vcomp (Frame.reify (whiskerLeftFrame word head))
             (FrameList.reify (whiskerLeftFrames word tail)))
           (.whiskerLeft word (.vcomp (Frame.reify head) (FrameList.reify tail)))
      -- head: reify (whiskerLeftFrame word head) ~ whiskerLeft word (reify head)
      have hhead : SesquiConv (Frame.reify (whiskerLeftFrame word head))
          (.whiskerLeft word (Frame.reify head)) := by
        -- reify (whiskerLeftFrame word head)
        --   = whiskerRight (whiskerLeft (append word head.left) (gen i)) head.right
        -- whiskerLeft word (reify head)
        --   = whiskerLeft word (whiskerRight (whiskerLeft head.left (gen i)) head.right)
        show SesquiConv
          (.whiskerRight (.whiskerLeft (OneCell.append word head.leftContext)
             (.gen head.genIndex)) head.rightContext)
          (.whiskerLeft word (.whiskerRight (.whiskerLeft head.leftContext
             (.gen head.genIndex)) head.rightContext))
        -- split the composite whisker on the left, then use commute
        have hcomposite : SesquiConv
            (.whiskerRight (.whiskerLeft (OneCell.append word head.leftContext)
               (.gen head.genIndex)) head.rightContext)
            (.whiskerRight (.whiskerLeft word (.whiskerLeft head.leftContext
               (.gen head.genIndex))) head.rightContext) :=
          SesquiConv.whiskerRightCongr
            (SesquiConv.whiskerLeftComposite word head.leftContext (.gen head.genIndex))
        exact SesquiConv.trans hcomposite
          (SesquiConv.whiskerCommute word head.rightContext
            (.whiskerLeft head.leftContext (.gen head.genIndex)))
      -- tail: IH
      have htail : SesquiConv (FrameList.reify (whiskerLeftFrames word tail))
          (.whiskerLeft word (FrameList.reify tail)) := sesquiConv_reify_whiskerLeft word tail
      -- combine: vcomp of the two, then pull whiskerLeft back out over vcomp
      have hcombine : SesquiConv
          (.vcomp (Frame.reify (whiskerLeftFrame word head))
             (FrameList.reify (whiskerLeftFrames word tail)))
          (.vcomp (.whiskerLeft word (Frame.reify head))
             (.whiskerLeft word (FrameList.reify tail))) :=
        SesquiConv.vcompCongr hhead htail
      exact SesquiConv.trans hcombine
        (SesquiConv.symm (SesquiConv.whiskerLeftVcomp word (Frame.reify head)
          (FrameList.reify tail)))

/-- Reify commutes with right-whiskering, up to convertibility. -/
theorem sesquiConv_reify_whiskerRight :
    ∀ (frames : FrameList) (word : OneCell),
      SesquiConv (FrameList.reify (whiskerRightFrames frames word))
        (.whiskerRight (FrameList.reify frames) word)
  | .nil, word =>
      SesquiConv.symm (SesquiConv.whiskerRightId word)
  | .cons head tail, word => by
      show SesquiConv (.vcomp (Frame.reify (whiskerRightFrame head word))
             (FrameList.reify (whiskerRightFrames tail word)))
           (.whiskerRight (.vcomp (Frame.reify head) (FrameList.reify tail)) word)
      have hhead : SesquiConv (Frame.reify (whiskerRightFrame head word))
          (.whiskerRight (Frame.reify head) word) := by
        show SesquiConv
          (.whiskerRight (.whiskerLeft head.leftContext (.gen head.genIndex))
             (OneCell.append head.rightContext word))
          (.whiskerRight (.whiskerRight (.whiskerLeft head.leftContext
             (.gen head.genIndex)) head.rightContext) word)
        exact SesquiConv.whiskerRightComposite
          (.whiskerLeft head.leftContext (.gen head.genIndex)) head.rightContext word
      have htail : SesquiConv (FrameList.reify (whiskerRightFrames tail word))
          (.whiskerRight (FrameList.reify tail) word) := sesquiConv_reify_whiskerRight tail word
      have hcombine : SesquiConv
          (.vcomp (Frame.reify (whiskerRightFrame head word))
             (FrameList.reify (whiskerRightFrames tail word)))
          (.vcomp (.whiskerRight (Frame.reify head) word)
             (.whiskerRight (FrameList.reify tail) word)) :=
        SesquiConv.vcompCongr hhead htail
      exact SesquiConv.trans hcombine
        (SesquiConv.symm (SesquiConv.whiskerRightVcomp word (Frame.reify head)
          (FrameList.reify tail)))

/-- Completeness core: every 2-cell is sesqui-convertible to the reification of
its ordered-frame normal form. -/
theorem sesquiConv_reify_normalize :
    ∀ cell : TwoCell, SesquiConv cell (FrameList.reify (normalize cell))
  | .id => SesquiConv.refl .id
  | .gen index => by
      -- normalize (gen i) = cons ⟨nil, i, nil⟩ nil
      -- reify = vcomp (whiskerRight (whiskerLeft nil (gen i)) nil) id
      show SesquiConv (.gen index)
        (.vcomp (.whiskerRight (.whiskerLeft OneCell.nil (.gen index)) OneCell.nil) .id)
      have h1 : SesquiConv
          (.vcomp (.whiskerRight (.whiskerLeft OneCell.nil (.gen index)) OneCell.nil) .id)
          (.whiskerRight (.whiskerLeft OneCell.nil (.gen index)) OneCell.nil) :=
        SesquiConv.vcompIdRight _
      have h2 : SesquiConv
          (.whiskerRight (.whiskerLeft OneCell.nil (.gen index)) OneCell.nil)
          (.whiskerLeft OneCell.nil (.gen index)) :=
        SesquiConv.whiskerRightNil _
      have h3 : SesquiConv (.whiskerLeft OneCell.nil (.gen index)) (.gen index) :=
        SesquiConv.whiskerLeftNil _
      exact SesquiConv.symm (SesquiConv.trans h1 (SesquiConv.trans h2 h3))
  | .vcomp first second => by
      show SesquiConv (.vcomp first second)
        (FrameList.reify (FrameList.append (normalize first) (normalize second)))
      have hcongr : SesquiConv (.vcomp first second)
          (.vcomp (FrameList.reify (normalize first)) (FrameList.reify (normalize second))) :=
        SesquiConv.vcompCongr (sesquiConv_reify_normalize first) (sesquiConv_reify_normalize second)
      exact SesquiConv.trans hcongr
        (SesquiConv.symm (sesquiConv_reify_append (normalize first) (normalize second)))
  | .whiskerLeft word body => by
      show SesquiConv (.whiskerLeft word body)
        (FrameList.reify (whiskerLeftFrames word (normalize body)))
      have hcongr : SesquiConv (.whiskerLeft word body)
          (.whiskerLeft word (FrameList.reify (normalize body))) :=
        SesquiConv.whiskerLeftCongr (sesquiConv_reify_normalize body)
      exact SesquiConv.trans hcongr
        (SesquiConv.symm (sesquiConv_reify_whiskerLeft word (normalize body)))
  | .whiskerRight body word => by
      show SesquiConv (.whiskerRight body word)
        (FrameList.reify (whiskerRightFrames (normalize body) word))
      have hcongr : SesquiConv (.whiskerRight body word)
          (.whiskerRight (FrameList.reify (normalize body)) word) :=
        SesquiConv.whiskerRightCongr (sesquiConv_reify_normalize body)
      exact SesquiConv.trans hcongr
        (SesquiConv.symm (sesquiConv_reify_whiskerRight (normalize body) word))

/-- Completeness of the decision: equal normal forms imply sesqui-convertibility.
Combined with `decideSesquiEq_of_sesquiConv` this makes `decideSesquiEq` a full
decision procedure for `SesquiConv`. -/
theorem sesquiConv_of_normalize_eq {first second : TwoCell} :
    normalize first = normalize second → SesquiConv first second := by
  intro heq
  have hfirst : SesquiConv first (FrameList.reify (normalize first)) :=
    sesquiConv_reify_normalize first
  have hsecond : SesquiConv second (FrameList.reify (normalize second)) :=
    sesquiConv_reify_normalize second
  rw [heq] at hfirst
  exact SesquiConv.trans hfirst (SesquiConv.symm hsecond)

/-- Full decision correctness: `decideSesquiEq` returns `true` iff the two
2-cells are sesqui-convertible. -/
theorem decideSesquiEq_iff_sesquiConv {first second : TwoCell} :
    decideSesquiEq first second = true ↔ SesquiConv first second := by
  apply Iff.intro
  · intro hdecide
    have heq : normalize first = normalize second :=
      FrameList.eq_of_beq (normalize first) (normalize second) hdecide
    exact sesquiConv_of_normalize_eq heq
  · exact decideSesquiEq_of_sesquiConv

/-! ## T4 — the interchange / premonoidal-centre wall

The decision above solves the FREE SESQUICATEGORY word problem: 2-cell equality
under the eleven whisker-action laws, with interchange EXCLUDED.  Adding the
interchange (Godement middle-four) law

  `(alpha |> d) ; (c' <| beta)  ~  (c <| beta) ; (alpha |> d)`

makes horizontal composition a bifunctor and upgrades the sesquicategory to a
strict 2-category.  Under interchange, two frames with *disjoint horizontal
support* commute, so the rigid ordered frame list collapses to a Mazurkiewicz
trace (the swap-invariant source-anchor normal form).  That coarser word
problem is a DIFFERENT decision, already shipped elsewhere in this library as
the free-2-cell trace decision (`decideTwoCellConvFull` /
`decidableSpineTraceEquiv_of`, routed through the source-anchor
canonicalization).  The `T5` false fire below exhibits exactly the collapse: a
would-be interchange swap that is EQUAL in the 2-category but DISTINCT here.

Two attacks burned on completing the interchange story *within this rigid frame
list*:

* Attack 1 — add an `interchange` constructor to `SesquiConv`.  It immediately
  breaks `normalize_eq_of_sesquiConv`: the swapped frame lists
  `[f_alpha, f_beta]` and `[f_beta, f_alpha]` are NOT `FrameList.beq`-equal,
  so the new law has NO normal-form witness.  Soundness against the ordered NF
  is FALSE by construction — the rigid order is exactly what interchange
  destroys.

* Attack 2 — quotient the frame list by adjacent disjoint-support swaps before
  comparing (an in-file trace canonicalization).  This is NOT the sesqui
  decision at all (it decides the strictly coarser 2-category relation), and
  deciding *which* frames may be swapped is the premonoidal-CENTRE question:
  characterizing the central (interchange-respecting) sub-family (Power–Robinson
  centre).  No decl anywhere in the library characterizes centrality; it is the
  genuine open extension, walled below. -/

/-- WALL: this file does NOT decide 2-cell equality up to interchange.  With
interchange the sesquicategory becomes a strict 2-category (disjoint frames
commute — the trace / Mazurkiewicz word problem, decided separately), and the
premonoidal CENTRE (which morphisms are central = interchange-respecting) is the
deep open extension. -/
def sqwHasInterchangeCompleteness : Bool := false

/-- WALL: no characterization of the premonoidal centre (central =
interchange-respecting 2-cells, Power–Robinson) is provided here. -/
def sqwHasPremonoidalCentreCharacterization : Bool := false

/-- Substrate landed flag: the free-sesquicategory ordered-whisker word problem
(carrier + NF + sound-and-complete decision, interchange excluded). -/
def sqwHasSesquiWordProblem : Bool := true

/-! ## T5 — ground fires -/

-- A whisker-functoriality instance decides EQUAL: `w <| (g0 ; g1)` vs `(w <| g0) ; (w <| g1)`.
example :
    decideSesquiEq
      (.whiskerLeft (.cons 5 .nil) (.vcomp (.gen 0) (.gen 1)))
      (.vcomp (.whiskerLeft (.cons 5 .nil) (.gen 0)) (.whiskerLeft (.cons 5 .nil) (.gen 1)))
      = true := rfl

-- Whisker of the identity 1-cell is a no-op: `nil <| g` decides equal to `g`.
example : decideSesquiEq (.whiskerLeft OneCell.nil (.gen 7)) (.gen 7) = true := rfl

-- Whisker of the identity 2-cell is the identity: `w <| id` decides equal to `id`.
example : decideSesquiEq (.whiskerLeft (.cons 3 .nil) .id) .id = true := rfl

-- THE INTERCHANGE-FAILS FIRE.  Under interchange (Godement) the two horizontal
-- orders of a right-whiskered `g0` and a left-whiskered `g1` at disjoint
-- objects are EQUAL; here they are DISTINCT ordered frame lists, so the
-- sesqui decision is FALSE.  This is the whole point of excluding interchange.
example :
    decideSesquiEq
      (.vcomp (.whiskerRight (.gen 0) (.cons 7 .nil)) (.whiskerLeft (.cons 9 .nil) (.gen 1)))
      (.vcomp (.whiskerLeft (.cons 9 .nil) (.gen 1)) (.whiskerRight (.gen 0) (.cons 7 .nil)))
      = false := rfl

-- Control: two genuinely different generators decide FALSE.
example : decideSesquiEq (.gen 0) (.gen 1) = false := rfl

-- Control: a cell is convertible to itself, decided TRUE.
example : decideSesquiEq (.vcomp (.gen 2) .id) (.gen 2) = true := rfl

end FX1Poly.Polygraph.Sesqui
