import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedGroupDecision

/-! # WP-TANGLE — tangles = braids meet cups/caps, over the shipped Brauer + signed-braid engines

A **tangle** is a morphism built from four generator kinds — positive crossing, negative crossing, cup, and cap
(plus the identity strand) — each fired at a boundary position, with the strand count changing at cups (`+2`) and
caps (`-2`).  This file BUILDS the tangle word-problem seed **on top of** two shipped, zero-axiom engines; it does
NOT rebuild either:

  * the **cup/cap + crossing matching engine** — `brauerDiagramOf` / `BrauerConv` / `decidableBrauerConv`
    (`Brauer/WiringDescStandardForm.lean`): a flat `m ⇒ n` Brauer/Temperley–Lieb diagram (a boundary perfect
    matching + loop count) with a TOTAL equal-diagram decision;
  * the **signed braid group `B_3` decision** — `BraidThreeSignedConv` / `decideBraidThreeGroupConv`
    (`WalkingBraid/BraidThreeSignedGroupDecision.lean`): the genuine braid group, whose inverses are NOT positive
    powers, decided via the signed Garside canon.

## What is shipped

  * **T1 — the tangle signature.**  `TngKind` / `TngTangleAtom` (a flat generator-list carrier, mirroring
    `BrauerAtom`), the input/output arity of each kind, the strand-count fold `tngWidthOf`, the well-scoping
    checker `tngWordWellScoped`, the identity tangle, and vertical composition `tngCompose = (· ++ ·)`.
    Composition preserves the width discipline (`tngCompose_width`, `tngWordWellScoped_append`).

  * **T2 — the combined invariant + soundness.**  `tngForget` maps a tangle to its UNDERLYING FLAT tangle
    (forget the crossing sign: `positiveCrossing`/`negativeCrossing ↦ crossingAt`), and `tngUnderlyingFlat` reads
    off its Brauer/TL `DiagramType`.  The tangle congruence `TngConv` is the pullback of the shipped `BrauerConv`
    along `tngForget`; SOUNDNESS (`tngConv_flatSound`) and — at the flat level — COMPLETENESS
    (`tngConv_flatComplete`) are one line each over the shipped `brauerConv_sound` / `brauerConv_complete`, giving
    `tngConv_iff_flatEq`.  Each Reidemeister/regular-isotopy move is exposed as a lemma: signed R2
    (`tngConv_signedR2_seed`), unsigned R2 (`tngConv_unsignedR2_seed`), R3 Yang–Baxter (`tngConv_r3_seed`), the
    two snakes / zig-zags (`tngConv_snake_seed`, `tngConv_snakeMirror_seed`), and the cap-slide
    (`tngConv_capSlide_seed`); the contextual interchange (Godement) is inherited verbatim through `tngConv_bridge`.
    The writhe (`tngWrithePositive` / `tngWritheNegative`) is the signed data the flat forget destroys.

  * **T3 — the two fragment decisions.**  PURE-FLAT (no crossings) and unsigned PURE-BRAID (any `n`) tangle
    equality are BOTH decided by the shipped matching decision (`tngConv_iff_flatEq` + `decideTngConvBool`).  The
    finer SIGNED pure-braid fragment at `n = 3` — which SEES over/under — reduces to the shipped `B_3` group
    decision: `tngSignedBraidWord` maps a pure-braid-3 tangle to `List BraidSignedAtom`, `TngBraidConv` is the
    pullback of `BraidThreeSignedConv`, decided by `decideTngBraidConv`.

  * **T4 — the honest wall.**  `tngHasFullTangleDecision = false`: the flat invariant is SOUND but NOT COMPLETE for
    the full (framed, oriented) tangle word problem.  The Brauer crossing is unsigned/involutive, so
    `tngUnderlyingFlat` forgets over-vs-under — no writhe, no Kauffman bracket / Reshetikhin–Turaev invariant; and
    even the flat combined completeness inherits the pass-5-arc cup/cap wall (`fxBrauer_hasBrauerCompleteness =
    false`).  The concrete witness: `tngConv_posX_negX_flatEqual` (the flat congruence IDENTIFIES a positive and a
    negative crossing) versus `tngBraid_posNeg_distinct` (the signed braid engine SEPARATES them).

Raw Lean 4 + Init only.  Structural recursion, no `omega` / `simp`-AC / `native_decide`; full-enum matches (no
`_ =>` wildcard over a split scrutinee).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph

/-! ## T1 — the tangle signature -/

/-- The four tangle generator kinds plus the identity strand: a POSITIVE crossing (over/under one way), a NEGATIVE
crossing (the reverse over/under), a `cup` (`0 ⇒ 2` unit), a `cap` (`2 ⇒ 0` counit), and the through-strand
`ident` (`1 ⇒ 1`).  A flat enum, so its equality is decidable and it drives the engine by pure data. -/
inductive TngKind where
  /-- A positive crossing `σ` (one over/under choice). -/
  | positiveCrossing
  /-- A negative crossing `σ⁻¹` (the reverse over/under). -/
  | negativeCrossing
  /-- The cup / unit `0 ⇒ 2`. -/
  | cup
  /-- The cap / counit `2 ⇒ 0`. -/
  | cap
  /-- The identity strand `1 ⇒ 1`. -/
  | ident
deriving DecidableEq

/-- ★ A **tangle atom**: a generator kind fired at a boundary `position` (the live index at which its input block
sits in the open-strand list).  A flat `Nat`-tagged datum, exactly the `BrauerAtom` shape every shipped engine
fold consumes. -/
structure TngTangleAtom where
  /-- The live boundary position at which the generator's input block sits. -/
  position : Nat
  /-- The generator kind. -/
  kind : TngKind
deriving DecidableEq

/-- The number of boundary strands a kind CONSUMES: `2` for a crossing / cap, `0` for a cup, `1` for the identity. -/
def tngInputCount : TngKind → Nat
  | .positiveCrossing => 2
  | .negativeCrossing => 2
  | .cup => 0
  | .cap => 2
  | .ident => 1

/-- The number of boundary strands a kind PRODUCES: `2` for a crossing / cup, `0` for a cap, `1` for the identity. -/
def tngOutputCount : TngKind → Nat
  | .positiveCrossing => 2
  | .negativeCrossing => 2
  | .cup => 2
  | .cap => 0
  | .ident => 1

/-- The width after firing one atom at a given width: consume its inputs, produce its outputs. -/
def tngWidthStep (width : Nat) (atom : TngTangleAtom) : Nat :=
  width - tngInputCount atom.kind + tngOutputCount atom.kind

/-- ★ The **strand count** after firing a whole tangle word from an initial `width` — the width discipline threaded
bottom-to-top.  Structural on the word. -/
def tngWidthOf : Nat → List TngTangleAtom → Nat
  | width, [] => width
  | width, atom :: rest => tngWidthOf (tngWidthStep width atom) rest

/-- ★ **The width fold splits over concatenation** — the strand count of `word1 ++ word2` is the count of `word2`
run from the count of `word1`.  Structural on `word1`, no arithmetic.  This is the T1 composition well-formedness:
if `word1 : w0 ⇒ w1` and `word2 : w1 ⇒ w2` then their composite `word1 ++ word2 : w0 ⇒ w2`. -/
theorem tngWidthOf_append : (word1 : List TngTangleAtom) → (width : Nat) → (word2 : List TngTangleAtom) →
    tngWidthOf width (word1 ++ word2) = tngWidthOf (tngWidthOf width word1) word2
  | [], _, _ => rfl
  | atom :: rest, width, word2 => tngWidthOf_append rest (tngWidthStep width atom) word2

/-- Left-associativity of boolean `and` (full-enum on the first argument, propext-free). -/
theorem tngBandAssoc : (first second third : Bool) →
    ((first && second) && third) = (first && (second && third))
  | true, _, _ => rfl
  | false, _, _ => rfl

/-- ★ A tangle word is **well-scoped** from an initial `width` when every atom's input block fits inside the live
strand count at the moment it fires (`position + inputCount ≤ width`), threaded through the width fold.  Structural
on the word; `Nat.ble` keeps it propext-free. -/
def tngWordWellScoped : Nat → List TngTangleAtom → Bool
  | _, [] => true
  | width, atom :: rest =>
      Nat.ble (atom.position + tngInputCount atom.kind) width
        && tngWordWellScoped (tngWidthStep width atom) rest

/-- ★ **Well-scoping splits over concatenation** — the composite `word1 ++ word2` is well-scoped from `width` iff
`word1` is well-scoped from `width` AND `word2` is well-scoped from the width `word1` reaches.  Structural on
`word1`; the cons case is one `tngBandAssoc`.  Together with `tngWidthOf_append` this is the full composition
well-formedness. -/
theorem tngWordWellScoped_append : (word1 : List TngTangleAtom) → (width : Nat) → (word2 : List TngTangleAtom) →
    tngWordWellScoped width (word1 ++ word2)
      = (tngWordWellScoped width word1 && tngWordWellScoped (tngWidthOf width word1) word2)
  | [], _, _ => rfl
  | atom :: rest, width, word2 => by
      show (Nat.ble (atom.position + tngInputCount atom.kind) width
              && tngWordWellScoped (tngWidthStep width atom) (rest ++ word2))
        = ((Nat.ble (atom.position + tngInputCount atom.kind) width
              && tngWordWellScoped (tngWidthStep width atom) rest)
            && tngWordWellScoped (tngWidthOf (tngWidthStep width atom) rest) word2)
      rw [tngWordWellScoped_append rest (tngWidthStep width atom) word2]
      exact (tngBandAssoc _ _ _).symm

/-- The **identity tangle** on `width` strands: one identity generator per strand. -/
def tngIdentity (width : Nat) : List TngTangleAtom :=
  (List.range width).map (fun position => { position := position, kind := .ident })

/-- **Vertical composition** of tangles is generator-word concatenation (the fold consumes the list; the width
discipline is carried by `tngWidthOf_append`). -/
def tngCompose (word1 word2 : List TngTangleAtom) : List TngTangleAtom := word1 ++ word2

/-- ★ **Vertical composition preserves the width discipline** — the composite runs `word2` from the width `word1`
reaches, so its output width is `word2`'s output over `word1`'s output.  A restatement of `tngWidthOf_append`. -/
theorem tngCompose_width (width : Nat) (word1 word2 : List TngTangleAtom) :
    tngWidthOf width (tngCompose word1 word2) = tngWidthOf (tngWidthOf width word1) word2 :=
  tngWidthOf_append word1 width word2

/-! ## T2 — the underlying flat tangle (forget the crossing sign) -/

/-- ★ **Forget the crossing sign** — map a tangle atom to its shipped `BrauerAtom`: BOTH crossing kinds collapse to
the single unsigned, involutive `crossingAt`; the cup / cap / identity map to their Brauer generators verbatim.
This is exactly the over-vs-under-forgetting map: the flat shadow of the tangle. -/
def tngForget (atom : TngTangleAtom) : BrauerAtom :=
  match atom.kind with
  | .positiveCrossing => crossingAt atom.position
  | .negativeCrossing => crossingAt atom.position
  | .cup => cupAt atom.position
  | .cap => capAt atom.position
  | .ident => identityStrandAt atom.position

/-- ★ The **underlying flat tangle** of a tangle word over `bottomCount` bottom strands: forget the crossing signs
and read off the shipped Brauer/Temperley–Lieb `DiagramType` (boundary matching + loop count).  The soundness map
into the combined invariant. -/
def tngUnderlyingFlat (bottomCount : Nat) (word : List TngTangleAtom) : DiagramType :=
  brauerDiagramOf bottomCount (word.map tngForget)

/-- ★ The **tangle congruence** — two tangles are congruent when their underlying flat tangles are `BrauerConv`-
convertible (the pullback of the shipped Brauer connectivity congruence along `tngForget`).  This is REGULAR
ISOTOPY of the flat shadow: closed under the five Reidemeister-style relations, the contextual interchange, and the
boundary-view whisker of the shipped `BrauerConv`. -/
def TngConv (bottomCount : Nat) (word1 word2 : List TngTangleAtom) : Prop :=
  BrauerConv bottomCount (word1.map tngForget) (word2.map tngForget)

/-- ★ **SOUNDNESS** — congruent tangles have equal combined invariant.  Directly the shipped `brauerConv_sound` on
the forgotten words. -/
theorem tngConv_flatSound {bottomCount : Nat} {word1 word2 : List TngTangleAtom}
    (conv : TngConv bottomCount word1 word2) :
    tngUnderlyingFlat bottomCount word1 = tngUnderlyingFlat bottomCount word2 :=
  brauerConv_sound conv

/-- ★ **FLAT COMPLETENESS** — tangles with equal underlying flat tangle are congruent.  Directly the shipped
`brauerConv_complete` on the forgotten words.  (This is completeness for the FLAT invariant; the full framed /
oriented tangle problem is the wall `tngHasFullTangleDecision`.) -/
theorem tngConv_flatComplete {bottomCount : Nat} {word1 word2 : List TngTangleAtom}
    (flatEq : tngUnderlyingFlat bottomCount word1 = tngUnderlyingFlat bottomCount word2) :
    TngConv bottomCount word1 word2 :=
  brauerConv_complete bottomCount (word1.map tngForget) (word2.map tngForget) flatEq

/-- ★ **`TngConv` is EXACTLY flat-diagram equality** — soundness and flat completeness together. -/
theorem tngConv_iff_flatEq (bottomCount : Nat) (word1 word2 : List TngTangleAtom) :
    TngConv bottomCount word1 word2
      ↔ tngUnderlyingFlat bottomCount word1 = tngUnderlyingFlat bottomCount word2 :=
  ⟨tngConv_flatSound, tngConv_flatComplete⟩

/-- ★ **`TngConv` is DECIDABLE** — the decision is flat-diagram equality via the shipped `decidableBrauerConv`. -/
def decideTngConv (bottomCount : Nat) (word1 word2 : List TngTangleAtom) :
    Decidable (TngConv bottomCount word1 word2) :=
  decidableBrauerConv bottomCount (word1.map tngForget) (word2.map tngForget)

instance instDecidableTngConv (bottomCount : Nat) (word1 word2 : List TngTangleAtom) :
    Decidable (TngConv bottomCount word1 word2) :=
  decideTngConv bottomCount word1 word2

/-- The tangle congruence decision as a `Bool` — `true` exactly when the two tangles share an underlying flat
tangle.  Reuses `decideBrauerConvBool` verbatim. -/
def decideTngConvBool (bottomCount : Nat) (word1 word2 : List TngTangleAtom) : Bool :=
  decideBrauerConvBool bottomCount (word1.map tngForget) (word2.map tngForget)

/-- The uniform bridge — a flat-diagram equality yields a `TngConv` (an alias of `tngConv_flatComplete`, the
generator used to exhibit each seed move). -/
theorem tngConv_of_flatEq {bottomCount : Nat} {word1 word2 : List TngTangleAtom}
    (flatEq : tngUnderlyingFlat bottomCount word1 = tngUnderlyingFlat bottomCount word2) :
    TngConv bottomCount word1 word2 :=
  tngConv_flatComplete flatEq

/-- Any `BrauerConv` on forgotten words IS a `TngConv` (definitional) — so the shipped contextual interchange
(Godement) move and the boundary-view whisker are inherited verbatim at the tangle level. -/
theorem tngConv_bridge {bottomCount : Nat} {word1 word2 : List TngTangleAtom}
    (conv : BrauerConv bottomCount (word1.map tngForget) (word2.map tngForget)) :
    TngConv bottomCount word1 word2 := conv

/-! ## T2 — the Reidemeister / regular-isotopy move lemmas (each a shipped `BrauerConv` constructor lifted) -/

/-- ★ **Signed R2** — a positive crossing then its negative cancel: `σ σ⁻¹ = id`.  Both crossings forget to the
same unsigned `crossingAt`, so the flat image is the shipped crossing involution. -/
theorem tngConv_signedR2_seed :
    TngConv 2 [⟨0, .positiveCrossing⟩, ⟨0, .negativeCrossing⟩] [] := by
  show BrauerConv 2 crossingInvolutionRelation.lhs crossingInvolutionRelation.rhs
  exact BrauerConv.crossingInvolution

/-- ★ **Unsigned R2** — two positive crossings cancel in the FLAT shadow: `σ σ = id` (the Brauer crossing is
involutive).  Distinct content from signed R2 only downstream of the sign, which the flat invariant discards. -/
theorem tngConv_unsignedR2_seed :
    TngConv 2 [⟨0, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩] [] := by
  show BrauerConv 2 crossingInvolutionRelation.lhs crossingInvolutionRelation.rhs
  exact BrauerConv.crossingInvolution

/-- ★ **R3 Yang–Baxter** — the braid relation on positive crossings: `(σ⊗1)(1⊗σ)(σ⊗1) = (1⊗σ)(σ⊗1)(1⊗σ)`.  The
forgotten words are exactly the shipped Yang–Baxter words, so this is `BrauerConv.yangBaxter` (no `brauerDiagramOf`
blow-up — the shipped staged proof is reused). -/
theorem tngConv_r3_seed :
    TngConv 3 [⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩]
      [⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩] := by
  show BrauerConv 3 yangBaxterRelation.lhs yangBaxterRelation.rhs
  exact BrauerConv.yangBaxter

/-- ★ **Snake / zig-zag (S1)** — a cup to the right of a strand then a cap straightens to the identity strand.  The
forgotten word is the shipped snake relation. -/
theorem tngConv_snake_seed :
    TngConv 1 [⟨1, .cup⟩, ⟨0, .cap⟩] [] := by
  show BrauerConv 1 snakeRelation.lhs snakeRelation.rhs
  exact BrauerConv.snake

/-- ★ **Snake / zig-zag mirror (S2)** — the mirror straightening. -/
theorem tngConv_snakeMirror_seed :
    TngConv 1 [⟨0, .cup⟩, ⟨1, .cap⟩] [] := by
  show BrauerConv 1 snakeMirrorRelation.lhs snakeMirrorRelation.rhs
  exact BrauerConv.snakeMirror

/-- ★ **Cap-slide (R1 naturality)** — a cap slides past a crossing.  The forgotten word is the shipped cap-slide
relation. -/
theorem tngConv_capSlide_seed :
    TngConv 3 [⟨1, .positiveCrossing⟩, ⟨0, .cap⟩] [⟨0, .positiveCrossing⟩, ⟨1, .cap⟩] := by
  show BrauerConv 3 capSlideRelation.lhs capSlideRelation.rhs
  exact BrauerConv.capSlide

/-! ## T2 — the writhe (the signed data the flat forget destroys) -/

/-- `1` on a positive crossing, `0` otherwise. -/
def tngPositiveMark : TngKind → Nat
  | .positiveCrossing => 1
  | .negativeCrossing => 0
  | .cup => 0
  | .cap => 0
  | .ident => 0

/-- `1` on a negative crossing, `0` otherwise. -/
def tngNegativeMark : TngKind → Nat
  | .positiveCrossing => 0
  | .negativeCrossing => 1
  | .cup => 0
  | .cap => 0
  | .ident => 0

/-- The number of POSITIVE crossings in a tangle word (half of the writhe datum the flat shadow forgets). -/
def tngWrithePositive : List TngTangleAtom → Nat
  | [] => 0
  | atom :: rest => tngPositiveMark atom.kind + tngWrithePositive rest

/-- The number of NEGATIVE crossings in a tangle word. -/
def tngWritheNegative : List TngTangleAtom → Nat
  | [] => 0
  | atom :: rest => tngNegativeMark atom.kind + tngWritheNegative rest

/-! ## T3(a) signed fragment — the pure-braid-3 tangle over the shipped `B_3` group decision -/

/-- Map a POSITIVE crossing at a braid-3 position to its signed atom (position `0 ↦ σ1`, `1 ↦ σ2`, `≥ 2` outside
`B_3` ↦ `[]`).  Full-enum on the `Nat` shape `0 | 1 | _+2`, propext-free. -/
def tngSignedPos : Nat → List BraidSignedAtom
  | 0 => [BraidSignedAtom.signedSigmaOne]
  | 1 => [BraidSignedAtom.signedSigmaTwo]
  | Nat.succ (Nat.succ _) => []

/-- Map a NEGATIVE crossing at a braid-3 position to its inverse signed atom. -/
def tngSignedNeg : Nat → List BraidSignedAtom
  | 0 => [BraidSignedAtom.signedSigmaOneInv]
  | 1 => [BraidSignedAtom.signedSigmaTwoInv]
  | Nat.succ (Nat.succ _) => []

/-- The signed-braid image of one tangle atom: a crossing becomes its (inverse) signed generator; a cup / cap /
identity has no braid content (`[]`).  For a genuine pure-braid-3 tangle only crossings at positions `0` / `1`
occur, so the image is exact. -/
def tngSignedBraidAtoms (atom : TngTangleAtom) : List BraidSignedAtom :=
  match atom.kind with
  | .positiveCrossing => tngSignedPos atom.position
  | .negativeCrossing => tngSignedNeg atom.position
  | .cup => []
  | .cap => []
  | .ident => []

/-- ★ The **signed-braid image** of a whole tangle word — concatenate the per-atom images bottom-to-top.  For a
pure-braid-3 tangle this is the corresponding `B_3` group word on `List BraidSignedAtom`. -/
def tngSignedBraidWord : List TngTangleAtom → List BraidSignedAtom
  | [] => []
  | atom :: rest => tngSignedBraidAtoms atom ++ tngSignedBraidWord rest

/-- ★ The **signed pure-braid congruence** — two pure-braid tangles are signed-congruent when their `B_3` group
words are `BraidThreeSignedConv`-related (the pullback of the shipped signed braid convertibility).  Unlike
`TngConv`, this SEES over/under: `σ` and `σ⁻¹` are separated. -/
def TngBraidConv (word1 word2 : List TngTangleAtom) : Prop :=
  BraidThreeSignedConv (tngSignedBraidWord word1) (tngSignedBraidWord word2)

/-- ★ **The signed pure-braid fragment is DECIDABLE** — via the shipped total `B_3` group decision
`decideBraidThreeGroupConv` on the signed-braid images. -/
def decideTngBraidConv (word1 word2 : List TngTangleAtom) : Decidable (TngBraidConv word1 word2) :=
  decideBraidThreeGroupConv (tngSignedBraidWord word1) (tngSignedBraidWord word2)

instance instDecidableTngBraidConv (word1 word2 : List TngTangleAtom) :
    Decidable (TngBraidConv word1 word2) :=
  decideTngBraidConv word1 word2

/-- The signed pure-braid decision as a `Bool` — `true` exactly when the two braid words are equal in `B_3`.
Full-enum on the `Decidable` result, propext-free. -/
def decideTngBraidConvBool (word1 word2 : List TngTangleAtom) : Bool :=
  match decideBraidThreeGroupConv (tngSignedBraidWord word1) (tngSignedBraidWord word2) with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ **R3 in the signed braid fragment** — the Yang–Baxter braid relation over `B_3`, via one shipped `braidRel`
constructor (cheap: no `brauerDiagramOf` union-find, just the group word). -/
theorem tngBraidConv_r3 :
    TngBraidConv [⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩]
      [⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩] := by
  show BraidThreeSignedConv
      [BraidSignedAtom.signedSigmaOne, BraidSignedAtom.signedSigmaTwo, BraidSignedAtom.signedSigmaOne]
      [BraidSignedAtom.signedSigmaTwo, BraidSignedAtom.signedSigmaOne, BraidSignedAtom.signedSigmaTwo]
  exact BraidThreeSignedConv.braidRel []

/-! ## T3 — the two fragment decisions, as fires

Pure-flat (no crossings) and unsigned pure-braid (any `n`) both decide by `decideTngConvBool` (= the shipped flat
matching decision); the signed pure-braid-3 fragment decides by `decideTngBraidConvBool`. -/

/-- ★ **Fragment fire — pure-flat via the matching engine.**  The cup/cap snake tangle is congruent to the identity
strand — decided `true` by the shipped matching decision. -/
theorem tngPureFlat_snake_decided : decideTngConvBool 1 [⟨1, .cup⟩, ⟨0, .cap⟩] [] = true := by decide

/-- ★ **Fragment fire — unsigned pure-braid via the matching engine.**  A double positive crossing is congruent to
the empty braid (unsigned R2) — decided `true`. -/
theorem tngPureBraid_doubleCrossing_decided :
    decideTngConvBool 2 [⟨0, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩] [] = true := by decide

/-! ## T5 — the ground fires -/

/-- ★ **Fire 1 — the underlying flat matching of a concrete cup-cap tangle.**  A cup then a cap over `0` bottom
strands closes ONE loop and leaves an empty boundary: `partner = []`, `loops = 1`.  By `rfl` (small union-find). -/
theorem tngFlat_cupCap_fire :
    tngUnderlyingFlat 0 [⟨0, .cup⟩, ⟨0, .cap⟩]
      = { bottomCount := 0, topCount := 0, partner := [], loops := 1 } := rfl

/-- ★ **Fire 2 — a pure-braid tangle equality via the signed braid engine.**  The Yang–Baxter braid words are equal
in `B_3` — decided `true`. -/
theorem tngBraid_yangBaxter_fire :
    decideTngBraidConvBool [⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩]
      [⟨1, .positiveCrossing⟩, ⟨0, .positiveCrossing⟩, ⟨1, .positiveCrossing⟩] = true := by decide

/-- ★ **Fire 3 — a pure-flat tangle equality via the matching engine.**  The snake straightens to the identity —
decided `true`. -/
theorem tngFlat_snake_fire : decideTngConvBool 1 [⟨1, .cup⟩, ⟨0, .cap⟩] [] = true := by decide

/-- ★ **Fire 4 (control) — two tangles with DIFFERENT flat matchings are NOT congruent.**  A single crossing is not
congruent to the identity pair — decided `false`. -/
theorem tngFlat_crossing_ne_identity_fire :
    decideTngConvBool 2 [⟨0, .positiveCrossing⟩] [⟨0, .ident⟩, ⟨1, .ident⟩] = false := by decide

/-- The writhe datum is genuinely read: a `σ σ⁻¹` word has one positive and one negative crossing. -/
theorem tngWrithe_fire :
    tngWrithePositive [⟨0, .positiveCrossing⟩, ⟨0, .negativeCrossing⟩] = 1
      ∧ tngWritheNegative [⟨0, .positiveCrossing⟩, ⟨0, .negativeCrossing⟩] = 1 :=
  ⟨rfl, rfl⟩

/-- The identity tangle preserves the strand count and is well-scoped (ground fire through the width fold). -/
theorem tngIdentity_fire :
    tngWidthOf 2 (tngIdentity 2) = 2 ∧ tngWordWellScoped 2 (tngIdentity 2) = true :=
  ⟨by decide, by decide⟩

/-! ## T4 — the honest wall: flat SOUND but not COMPLETE for the full tangle problem

The flat invariant forgets over/under; the two fires below make the gap CONCRETE — the flat congruence identifies a
positive and a negative crossing, while the signed braid engine separates them. -/

/-- ★ **The flat congruence IDENTIFIES a positive and a negative crossing** — both forget to the same unsigned
`crossingAt`, so `tngUnderlyingFlat` cannot see over-vs-under.  By `rfl` (both sides the SAME flat diagram). -/
theorem tngConv_posX_negX_flatEqual : TngConv 2 [⟨0, .positiveCrossing⟩] [⟨0, .negativeCrossing⟩] :=
  tngConv_of_flatEq rfl

/-- ★ **The signed braid engine SEPARATES the same positive and negative crossing** — `σ ≠ σ⁻¹` in `B_3`, decided
`false`.  Contrast with `tngConv_posX_negX_flatEqual`: this is the exact content the flat invariant loses, hence no
writhe / no Kauffman bracket from the flat shadow alone. -/
theorem tngBraid_posNeg_distinct :
    decideTngBraidConvBool [⟨0, .positiveCrossing⟩] [⟨0, .negativeCrossing⟩] = false := by decide

/-! ## Honesty markers -/

/-- **Honesty marker — the tangle signature is SHIPPED (T1).**  `TngKind` / `TngTangleAtom` (the flat generator-
list carrier), the arity `tngInputCount` / `tngOutputCount`, the width fold `tngWidthOf`, the well-scoping checker
`tngWordWellScoped`, the identity tangle `tngIdentity`, and vertical composition `tngCompose`.  Composition
preserves the width discipline (`tngWidthOf_append` / `tngCompose_width` / `tngWordWellScoped_append`).  `= true`. -/
def tngHasTangleSignature : Bool := true

/-- **Honesty marker — the combined invariant + soundness is SHIPPED (T2).**  `tngForget` / `tngUnderlyingFlat`
give the underlying FLAT tangle (a Brauer/TL `DiagramType`); `TngConv` is the pullback of the shipped `BrauerConv`;
`tngConv_flatSound` is soundness, `tngConv_flatComplete` flat completeness, `tngConv_iff_flatEq` their conjunction,
`decideTngConv` the decision.  Every Reidemeister/regular-isotopy move ships as a lemma (`tngConv_signedR2_seed`,
`tngConv_unsignedR2_seed`, `tngConv_r3_seed`, `tngConv_snake_seed`, `tngConv_snakeMirror_seed`,
`tngConv_capSlide_seed`), the contextual interchange inherited via `tngConv_bridge`.  The writhe
(`tngWrithePositive` / `tngWritheNegative`) is the forgotten signed datum.  `= true`. -/
def tngHasCombinedInvariantSoundness : Bool := true

/-- **Honesty marker — the SIGNED pure-braid-3 fragment decision is SHIPPED (T3a).**  `tngSignedBraidWord` maps a
pure-braid-3 tangle to `List BraidSignedAtom`; `TngBraidConv` is the pullback of the shipped `BraidThreeSignedConv`;
`decideTngBraidConv` / `decideTngBraidConvBool` decide it via the shipped total `B_3` group decision.  This SEES
over/under (`tngBraid_posNeg_distinct`).  `= true`. -/
def tngHasPureBraidDecision : Bool := true

/-- **Honesty marker — the PURE-FLAT (and unsigned any-`n` pure-braid) fragment decision is SHIPPED (T3b).**  Both
decide by `decideTngConvBool` — the shipped flat matching decision — via `tngConv_iff_flatEq`
(`tngPureFlat_snake_decided`, `tngPureBraid_doubleCrossing_decided`).  `= true`. -/
def tngHasPureFlatDecision : Bool := true

/-- ★ **Honesty marker — the FULL tangle word problem is a WALL (T4): `= false`.**  The combined invariant
`tngUnderlyingFlat` is SOUND (`tngConv_flatSound`) but NOT COMPLETE for framed / oriented tangle equality.  The
precise obstruction: the shipped Brauer crossing is UNSIGNED / involutive, so `tngForget` collapses
`positiveCrossing` and `negativeCrossing` to the same `crossingAt` — over-vs-under is destroyed
(`tngConv_posX_negX_flatEqual` identifies what `tngBraid_posNeg_distinct` separates).  Consequently there is NO
writhe and NO Kauffman-bracket / Reshetikhin–Turaev state-sum readable from the flat shadow: a complete tangle/knot
invariant needs the over/under sign the flat matching discards, and the bracket is a Laurent-polynomial state-sum,
not a finite matching.  Even the FLAT combined completeness inherits the pass-5-arc cup/cap wall
(`fxBrauer_hasBrauerCompleteness = false`, the `i<k<j<l` interleaved cup/cap driver-fold).  The genuine `B_3` group
decision recovers over/under only in the crossing-only fragment at strand count `3`; full Reidemeister completeness
across mixed crossings + cups/caps at every strand count is the research wall.  `= false`. -/
def tngHasFullTangleDecision : Bool := false

end FX1Poly.Polygraph
