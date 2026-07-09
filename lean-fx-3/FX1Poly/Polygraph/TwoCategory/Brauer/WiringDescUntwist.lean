import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraighteningGap

/-! # WP-BRAUER-4 r3 — the seven-relation extension: untwist closure, wall DISSOLUTION, extended-conv soundness

The r2 wall (`Brauer/WiringDescStraighteningGap.lean`) machine-refuted that the FIVE relations under-generate the free
Brauer category: `crossingParity` (total crossing count mod 2) is invariant along `BrauerConvFree` — the honest
over-approximation of the five-relation closure — yet the cup untwist `[cupAt 0, crossingAt 0]` vs `[cupAt 0]` is an
EQUAL Brauer diagram whose parity FLIPS.  So the five relations present a proper Z/2 cover, not the Brauer category
(Lehrer–Zhang, arXiv:1207.5889, use SEVEN relations).

This file lands the r3 fix the wall named.  `Brauer/WiringDesc.lean` already added the two Lehrer–Zhang untwist DATA
rows (`cupUntwistRelation` = 2.5∗, `capUntwistRelation` = 2.5) with their diagram-soundness witnesses; here we:

  * **Extend the over-approximation** — `BrauerConvFree7` = `BrauerConvFree` (via `ofFree`) closed under equivalence
    and congruence PLUS the two untwist rows at any horizontal offset.  ADDITIVE: `BrauerConvFree` and all r2 wall
    theorems are untouched, and `BrauerConvFree7` genuinely CONTAINS `BrauerConvFree` (`brauerConvFree7_ofFree`).
  * **DISSOLVE the r2 wall** — `crossingParity` is provably NOT a `BrauerConvFree7` invariant
    (`crossingParity_not_brauerConvFree7_invariant`): the `cupUntwist` constructor relates a parity-1 word to a
    parity-0 word.  The BEFORE / AFTER is crisp: the untwist pair is `not BrauerConvFree` (r2,
    `brauerUntwist_not_brauerConvFree`, still valid) but IS `BrauerConvFree7` (`brauerConvFree7_cupUntwist_derivable`).
    This is exactly the designed effect — `crossingParity` is CORRECTLY no longer an invariant of the seven-relation
    closure; that was the whole point of adding the untwists.
  * **Extend the diagram-sound convertibility** — each untwist, whiskered in ARBITRARY horizontal context, is
    `BrauerConv`-convertible (`brauerConv_cupUntwist_inWiderContext` / `brauerConv_capUntwist_inWiderContext`) via the
    relation-agnostic keystone `brauerConv_relation_inContext`, fed the two new seed-soundness legs.  Since
    `brauerConv_sound` (unchanged) makes `BrauerConv` diagram-sound, `fxBrauer_hasBrauerSoundness` STAYS `true` over
    the strengthened seven-relation presentation (strengthen, never weaken).

## The residual — the constructive straightening NF, no surviving character

`crossingParity` was the r2 obstruction; it is gone.  Classically the seven Lehrer–Zhang relations DO present the
Brauer category (arXiv:1207.5889, Theorem 2.6(2)), so NO second under-generation character survives — there is no
"relation 8" to wall.  The residual `fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean`) STAYS `false` honestly,
but it is now purely CONSTRUCTIVE (the classical straightening normal form: cups-top / caps-bottom sort via
snake + cap-slide + untwist, the crossing block canonicalized by Matsumoto's insertion — which needs the inversion-count
measure named by `fxBrauer_hasCrossingOnlyStraightening`, not word-length + crossing-count), NOT an obstruction.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `BrauerConvFree7` — the seven-relation over-approximation (ADDITIVE over `BrauerConvFree`)

`BrauerConvFree` (r2) is embedded verbatim via `ofFree`, then closed under equivalence (`symm` / `trans`) and
congruence (`whiskerLeft` / `whiskerRight`) together with the two untwist rows at ANY horizontal offset.  It is
DELIBERATELY generous (no soundness side-condition on whiskering, exactly like `BrauerConvFree`) — its purpose is the
wall-DISSOLUTION demo, not soundness.  Since it contains `BrauerConvFree` and the two untwists, it over-approximates
the true seven-relation closure. -/
inductive BrauerConvFree7 : List BrauerAtom → List BrauerAtom → Prop
  /-- Embed the whole five-relation over-approximation `BrauerConvFree` (reflexivity, symmetry, transitivity, the five
  relations at any offset, interchange, both whiskerings). -/
  | ofFree {wordLeft wordRight : List BrauerAtom} :
      BrauerConvFree wordLeft wordRight → BrauerConvFree7 wordLeft wordRight
  /-- Symmetry (closes the two untwist rows under symmetry). -/
  | symm {wordLeft wordRight : List BrauerAtom} :
      BrauerConvFree7 wordLeft wordRight → BrauerConvFree7 wordRight wordLeft
  /-- Transitivity. -/
  | trans {wordLeft wordMid wordRight : List BrauerAtom} :
      BrauerConvFree7 wordLeft wordMid → BrauerConvFree7 wordMid wordRight → BrauerConvFree7 wordLeft wordRight
  /-- ★ R6 cup untwist `σ ∘ cup = cup` at horizontal offset `shift`. -/
  | cupUntwist (shift : Nat) :
      BrauerConvFree7 (shiftWord shift cupUntwistRelation.lhs) (shiftWord shift cupUntwistRelation.rhs)
  /-- ★ R7 cap untwist `cap ∘ σ = cap` at horizontal offset `shift`. -/
  | capUntwist (shift : Nat) :
      BrauerConvFree7 (shiftWord shift capUntwistRelation.lhs) (shiftWord shift capUntwistRelation.rhs)
  /-- Vertical congruence on the left: prepend a common word. -/
  | whiskerLeft {wordLeft wordRight : List BrauerAtom} (prefixWord : List BrauerAtom) :
      BrauerConvFree7 wordLeft wordRight → BrauerConvFree7 (prefixWord ++ wordLeft) (prefixWord ++ wordRight)
  /-- Vertical congruence on the right: append a common word. -/
  | whiskerRight {wordLeft wordRight : List BrauerAtom} (suffixWord : List BrauerAtom) :
      BrauerConvFree7 wordLeft wordRight → BrauerConvFree7 (wordLeft ++ suffixWord) (wordRight ++ suffixWord)

/-- `BrauerConvFree7` genuinely CONTAINS `BrauerConvFree` — the extension is additive (nothing of the old closure is
lost), just `ofFree`. -/
theorem brauerConvFree7_ofFree {wordLeft wordRight : List BrauerAtom}
    (conv : BrauerConvFree wordLeft wordRight) : BrauerConvFree7 wordLeft wordRight :=
  BrauerConvFree7.ofFree conv

/-! ## Non-vacuity — the two untwists ARE derivable in the seven-relation closure -/

/-- ★ **The cup untwist is derivable in `BrauerConvFree7`** (at offset `0`) — the exact pair the r2 wall proved
UNreachable by the five relations.  `shiftWord 0` is definitionally the identity. -/
theorem brauerConvFree7_cupUntwist_derivable :
    BrauerConvFree7 [cupAt 0, crossingAt 0] [cupAt 0] :=
  BrauerConvFree7.cupUntwist 0

/-- ★ **The cap untwist is derivable in `BrauerConvFree7`** (at offset `0`). -/
theorem brauerConvFree7_capUntwist_derivable :
    BrauerConvFree7 [crossingAt 0, capAt 0] [capAt 0] :=
  BrauerConvFree7.capUntwist 0

/-- The old five relations still embed — R2 involutivity at the seed, via `ofFree`.  Non-vacuity that the extension
retains the old closure. -/
theorem brauerConvFree7_crossingInvolution_seed :
    BrauerConvFree7 [crossingAt 0, crossingAt 0] [] :=
  BrauerConvFree7.ofFree brauerConvFree_crossingInvolution_seed

/-! ## The DISSOLUTION — `crossingParity` is no longer an invariant of the seven-relation closure

The r2 wall stood on `crossingParity_brauerConvFree`: `crossingParity` is invariant along the FIVE-relation
over-approximation `BrauerConvFree` (still valid — untouched).  Adding the untwist rows DISSOLVES that wall: the
`cupUntwist` constructor relates a parity-1 word to a parity-0 word, so `crossingParity` is provably NOT a
`BrauerConvFree7` invariant.  This is the designed effect — the untwist is exactly the diagram-equal, parity-flipping
pair the wall exhibited, now made derivable. -/

/-- ★★ **THE r2 WALL IS DISSOLVED** — `crossingParity` is NOT a `BrauerConvFree7` invariant.  If it were, the
`cupUntwist` constructor (relating `[cupAt 0, crossingAt 0]`, parity `1`, to `[cupAt 0]`, parity `0`) would force
`1 = 0` (`brauerUntwist_parity_ne`).  So the seven-relation closure correctly no longer respects the crossing-count
parity character — that character was the r2 under-generation obstruction, and it is gone. -/
theorem crossingParity_not_brauerConvFree7_invariant :
    ¬ (∀ (wordLeft wordRight : List BrauerAtom),
        BrauerConvFree7 wordLeft wordRight → crossingParity wordLeft = crossingParity wordRight) :=
  fun invariant => brauerUntwist_parity_ne
    (invariant [cupAt 0, crossingAt 0] [cupAt 0] (BrauerConvFree7.cupUntwist 0))

/-- The crisp BEFORE / AFTER of the dissolution: the untwist pair is NOT reachable by the five relations
(`brauerUntwist_not_brauerConvFree`, r2, unchanged) but IS reachable once the untwist row is added
(`brauerConvFree7_cupUntwist_derivable`).  So the extension is genuinely proper — it reaches a pair the five-relation
closure provably cannot. -/
theorem brauerConvFree7_strictly_extends_brauerConvFree :
    (¬ BrauerConvFree [cupAt 0, crossingAt 0] [cupAt 0])
      ∧ BrauerConvFree7 [cupAt 0, crossingAt 0] [cupAt 0] :=
  ⟨brauerUntwist_not_brauerConvFree, brauerConvFree7_cupUntwist_derivable⟩

/-! ## Extended-conv SOUNDNESS — each untwist whiskered in arbitrary context is `BrauerConv` (hence diagram-sound)

The diagram-sound convertibility `BrauerConv` (`Brauer/WiringDescConv.lean`) already equals diagram equality
(`brauerConv_iff_diagram`), so it ALREADY contains the untwists; here we exhibit them as first-class relation firings
through the SAME relation-agnostic keystone the five relations use (`brauerConv_relation_inContext`), fed the two new
seed-soundness legs (`cupUntwist_diagram_sound` / `capUntwist_diagram_sound`).  This is the concrete sense in which
`fxBrauer_hasBrauerSoundness` (unchanged, riding `brauerConv_sound`) now covers the SEVEN-relation presentation. -/

/-- ★ **The cup untwist, fired at offset `1` in a width-2 boundary (`1 + (0 + 1)`), is `BrauerConv`-convertible.**  A
boundary-CHANGING firing of R6 through the two-sided pad congruence keystone. -/
theorem brauerConv_cupUntwist_inWiderContext :
    BrauerConv 2 ([] ++ shiftBrauerWord 1 cupUntwistRelation.lhs)
      ([] ++ shiftBrauerWord 1 cupUntwistRelation.rhs) :=
  brauerConv_relation_inContext 2 (by decide) [] (BrauerWordInRange.nil 2) 1 0 1
    cupUntwistRelation.lhs cupUntwistRelation.rhs (by decide)
    (BrauerWordInRange.cons (cupAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
    (BrauerWordInRange.cons (cupAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))
    rfl rfl cupUntwist_diagram_sound

/-- ★ **The cap untwist, fired at offset `1` in a width-4 boundary (`1 + (2 + 1)`), is `BrauerConv`-convertible.**  A
boundary-CHANGING firing of R7 through the keystone. -/
theorem brauerConv_capUntwist_inWiderContext :
    BrauerConv 4 ([] ++ shiftBrauerWord 1 capUntwistRelation.lhs)
      ([] ++ shiftBrauerWord 1 capUntwistRelation.rhs) :=
  brauerConv_relation_inContext 4 (by decide) [] (BrauerWordInRange.nil 4) 1 2 1
    capUntwistRelation.lhs capUntwistRelation.rhs (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (capAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 0)))
    (BrauerWordInRange.cons (capAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 0))
    rfl rfl capUntwist_diagram_sound

/-- The seed untwist firings genuinely relate DISTINCT words (offset `1`, both nonempty vs their reduced form) — the
extended-conv soundness witnesses are proper, inhabited firings. -/
theorem brauerConv_untwist_inWiderContext_distinct :
    ([] ++ shiftBrauerWord 1 cupUntwistRelation.lhs) ≠ ([] ++ shiftBrauerWord 1 cupUntwistRelation.rhs)
      ∧ ([] ++ shiftBrauerWord 1 capUntwistRelation.lhs) ≠ ([] ++ shiftBrauerWord 1 capUntwistRelation.rhs) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the r2 straightening WALL is DISSOLVED.**  `BrauerConvFree7` extends the r2 over-approximation
`BrauerConvFree` (additively, via `ofFree`) with the two Lehrer–Zhang untwist rows at any offset, and
`crossingParity_not_brauerConvFree7_invariant` proves `crossingParity` is CORRECTLY no longer an invariant of the
seven-relation closure — the `cupUntwist` constructor relates the parity-1 word `[cupAt 0, crossingAt 0]` to the
parity-0 word `[cupAt 0]`.  The BEFORE / AFTER is machine-checked: `brauerConvFree7_strictly_extends_brauerConvFree`
pairs the r2 non-reachability (`brauerUntwist_not_brauerConvFree`, unchanged) with the new reachability
(`brauerConvFree7_cupUntwist_derivable`).  The r2 wall theorems stay valid (they are about the OLD five-relation
closure); this marker records that the crossing-parity obstruction they exhibited is now removed by design.  `= true`. -/
def fxBrauer_hasBrauerUntwistWallDissolved : Bool := true

/-- ★ **Honesty marker — diagram-soundness now covers the SEVEN-relation presentation.**  Each untwist, whiskered in
arbitrary horizontal context, is `BrauerConv`-convertible via the relation-agnostic keystone
`brauerConv_relation_inContext` (`brauerConv_cupUntwist_inWiderContext` / `brauerConv_capUntwist_inWiderContext`, both
genuinely boundary-CHANGING), fed the two new seed-soundness legs.  Since `brauerConv_sound` (unchanged) makes
`BrauerConv` diagram-sound and `brauerConv_iff_diagram` shows `BrauerConv` = diagram equality, `fxBrauer_hasBrauerSoundness`
STAYS `true` over the strengthened seven-relation presentation — soundness is strengthened, never weakened.  `= true`. -/
def fxBrauer_hasSevenRelationConvSoundness : Bool := true

/-- **Honesty marker — COMPLETENESS stays `false`, but the residual is now purely CONSTRUCTIVE (no surviving
character).**  The r2 obstruction (`crossingParity`) is dissolved, and classically the seven Lehrer–Zhang relations DO
present the Brauer category (arXiv:1207.5889, Theorem 2.6(2)) — so NO second under-generation character survives; there
is no "relation 8" to wall.  What remains for `fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean`) is the
classical straightening normal form: cups-top / caps-bottom sort (snake + cap-slide + untwist) with the crossing block
canonicalized by Matsumoto's insertion — which the recon showed needs the INVERSION-COUNT measure named by
`fxBrauer_hasCrossingOnlyStraightening` (word-length + crossing-count does NOT decrease under the R3 reorder).  That is
constructive work over further rounds, NOT an obstruction — the flag is honestly `false`, not walled.  `= false`. -/
def fxBrauer_hasBrauerStraighteningNFResidual : Bool := false

end FX1Poly.Polygraph
