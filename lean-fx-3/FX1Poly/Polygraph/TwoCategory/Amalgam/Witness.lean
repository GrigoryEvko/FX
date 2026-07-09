import FX1Poly.Polygraph.TwoCategory.Amalgam.InterleavingNF
import FX1Poly.Polygraph.TwoCategory.Amalgam.Dispatch

/-! # Polygraph/TwoCategory/Amalgam/Witness — the involution + monad pushout, block-decompositions that COMPUTE

The concrete witness for the WP-AMALG-1 substrate: instantiate the mode-signature pushout (`Pushout.lean`) at two
DECIDED walking doctrines sharing a single mode, then EXERCISE the interleaving normal form (`InterleavingNF.lean`)
and the disjoint-generator precondition of the dispatch statement (`Dispatch.lean`) on concrete words — every
check closing by `rfl` (definitional computation), plus `#eval` for observability.

## The two components (both `modeCount = 1`, DISJOINT endo-generators)

  * **`involutionComputad`** — the `ModeComputad` presentation of the walking-involution seed
    (`WalkingInvolution/InvolutionSeed.involutionModeSignature`): one object `point`, one endo-1-generator `s`, NO
    generating 2-cells.  Honesty note: the involution's relation `s.s = id` lives at the 1-CELL level
    (`InvolutionOneCellConv`), so the computad's 2-generator list is genuinely empty — matching the seed's
    `twoCell := Empty`.
  * **`monadComputad`** — the `ModeComputad` presentation of the walking-monad seed
    (`Computad/MonadSeed.monadModeSignature`): one object `point`, one endo-1-generator `t`, and the two generating
    2-cells `eta : id ⇒ t` (word `[] ⇒ [t]`) and `mu : t.t ⇒ t` (word `[t,t] ⇒ [t]`).

They share the single mode `point` and have DISJOINT 1-generators (`s` vs `t`), so their pushout `involution +_M
monad` is the cleanest shared-mode amalgam: one mode, two 1-generators (`s @ 0`, `t @ 1`), the monad's two
2-generators retagged into the right index range.  This is exactly the Nyberg-Brodda free-product setting.

## What is exercised here (each `rfl`, so it COMPUTES; plus `#eval` observability)

  * **`involutionMonadPushout`** — the concrete pushout computad; its `dimensionProfile` is `(1, 2, 2)` by `rfl`.
  * **`witnessWordDecompose`** — `blockDecompose` on the concrete alternating word `s t s t t` returns the four
    maximal same-component blocks `[(s), (t), (s), (t t)]`, proven by `rfl` (NON-VACUOUS: it genuinely reduces).
  * **`witnessRecomposeSound` / `witnessAlternates` / `witnessBlocksNonempty`** — the three NF invariants
    instantiated at the witness word.
  * **`involutionMonadPushout_disjoint`** — the disjoint-generator precondition of `DispatchDecidability` HOLDS
    for this pushout (`computadGeneratorsDisjoint = true` by `rfl`): the monad's retagged `eta` / `mu` relations
    mention ONLY component-2 letters.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## The two component computads (shared single mode, disjoint endo-generators) -/

/-- The `ModeComputad` presentation of the walking-involution seed — one mode, one endo-1-generator `s`, no
generating 2-cells (the involution's `s.s = id` law is 1-cell-level). -/
def involutionComputad : ModeComputad where
  modeCount := 1
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators := []

/-- The `ModeComputad` presentation of the walking-monad seed — one mode, one endo-1-generator `t`, and the two
generating 2-cells `eta : id ⇒ t` (word `[] ⇒ [t]`) and `mu : t.t ⇒ t` (word `[t,t] ⇒ [t]`). -/
def monadComputad : ModeComputad where
  modeCount := 1
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators :=
    [ { src := ⟨0, by decide⟩, tgt := ⟨0, by decide⟩, lhs := [], rhs := [⟨0, by decide⟩] },
      { src := ⟨0, by decide⟩, tgt := ⟨0, by decide⟩,
        lhs := [⟨0, by decide⟩, ⟨0, by decide⟩], rhs := [⟨0, by decide⟩] } ]

/-- The two components genuinely share their mode set (both `modeCount = 1`). -/
def involutionMonadSameModes : involutionComputad.modeCount = monadComputad.modeCount := rfl

/-! ## The concrete pushout -/

/-- ★ The **witness pushout** `involution +_M monad` — one mode, two 1-generators (`s @ 0`, `t @ 1`), the monad's
two 2-generators retagged into component 2. -/
def involutionMonadPushout : ModeComputad :=
  pushoutShared involutionComputad monadComputad involutionMonadSameModes

/-- The component-1 boundary (the split point for the interleaving NF and the disjointness check) — the involution
component contributes `involutionComputad.modalityGenerators.length = 1` generators. -/
def involutionMonadSplit : Nat := involutionComputad.modalityGenerators.length

/-- Profile faithfulness: the involution computad presents one mode, one 1-generator, zero 2-generators. -/
theorem involutionComputad_profile : involutionComputad.dimensionProfile = (1, 1, 0) := rfl

/-- Profile faithfulness: the monad computad presents one mode, one 1-generator, two 2-generators (eta, mu). -/
theorem monadComputad_profile : monadComputad.dimensionProfile = (1, 1, 2) := rfl

/-- ★ The pushout presents one mode, TWO 1-generators (the disjoint `s` + `t`), TWO 2-generators (the monad's
retagged eta + mu) — the free-product / coproduct dimension count. -/
theorem involutionMonadPushout_profile : involutionMonadPushout.dimensionProfile = (1, 2, 2) := rfl

/-! ## The two combined 1-generators as letters -/

/-- The letter `s` (component 1) in the pushout's generator alphabet — the left embedding of the involution's
generator, index `0`. -/
def sLetter : Fin involutionMonadPushout.modalityGenerators.length :=
  embedLeftLetter involutionComputad monadComputad involutionMonadSameModes ⟨0, by decide⟩

/-- The letter `t` (component 2) in the pushout's generator alphabet — the right embedding of the monad's
generator, index `1` (shifted by `len1 = 1`). -/
def tLetter : Fin involutionMonadPushout.modalityGenerators.length :=
  embedRightLetter involutionComputad monadComputad involutionMonadSameModes ⟨0, by decide⟩

/-- The letter `s` sits in component 1 (tag `true`). -/
theorem sLetter_component :
    combinedGeneratorComponent involutionComputad monadComputad involutionMonadSameModes sLetter = true :=
  rfl

/-- The letter `t` sits in component 2 (tag `false`). -/
theorem tLetter_component :
    combinedGeneratorComponent involutionComputad monadComputad involutionMonadSameModes tLetter = false :=
  rfl

/-! ## Block decomposition on a concrete alternating word — every check `rfl` -/

/-- The witness word `s t s t t` over the pushout alphabet — a genuine alternating mixture of both components. -/
def witnessWord : List (Fin involutionMonadPushout.modalityGenerators.length) :=
  [sLetter, tLetter, sLetter, tLetter, tLetter]

/-- ★ **The block decomposition COMPUTES** — `blockDecompose` on `s t s t t` returns the four maximal same-component
blocks `[(s), (t), (s), (t t)]`, closing by `rfl` (NON-VACUOUS: the alternating factorisation genuinely reduces on
concrete data).  The last block `(t t)` merges the two adjacent `t`s; the alternation of the tags is visible. -/
theorem witnessWordDecompose :
    blockDecompose involutionMonadSplit witnessWord
      = [(true, [sLetter]), (false, [tLetter]), (true, [sLetter]), (false, [tLetter, tLetter])] :=
  rfl

/-- The soundness invariant instantiated at the witness word — recomposing the blocks recovers `s t s t t`. -/
theorem witnessRecomposeSound :
    recompose (blockDecompose involutionMonadSplit witnessWord) = witnessWord :=
  blockDecompose_sound involutionMonadSplit witnessWord

/-- The alternation invariant instantiated at the witness word — the four blocks alternate `true false true false`. -/
theorem witnessAlternates :
    isAlternating (blockDecompose involutionMonadSplit witnessWord) = true :=
  blockDecompose_alternates involutionMonadSplit witnessWord

/-- The non-degeneracy invariant instantiated at the witness word — every block is non-empty. -/
theorem witnessBlocksNonempty :
    allBlocksNonempty (blockDecompose involutionMonadSplit witnessWord) = true :=
  blockDecompose_blocksNonempty involutionMonadSplit witnessWord

/-! ## The dispatch precondition holds for this pushout -/

/-- ★ **The disjoint-generator precondition of `DispatchDecidability` HOLDS** for the witness pushout — every
2-generator (the monad's retagged `eta` / `mu`) is component-pure at the split point (mentions ONLY component-2
letters), so `computadGeneratorsDisjoint = true` by `rfl`.  This is the load-bearing Baader-Tinelli hypothesis,
witnessed concretely: the amalgam has NO relation across the component boundary. -/
theorem involutionMonadPushout_disjoint :
    computadGeneratorsDisjoint involutionMonadSplit involutionMonadPushout = true :=
  rfl

/-! ## Observability -/

-- The block decomposition of the witness word, letters shown by their generator index: expect
-- `[(true, [0]), (false, [1]), (true, [0]), (false, [1, 1])]` (s @ 0, t @ 1; the two adjacent `t`s merged).
#eval (blockDecompose involutionMonadSplit witnessWord).map (fun block => (block.1, block.2.map Fin.val))

-- The pushout's dimension profile: expect `(1, 2, 2)` — one mode, two 1-generators, two 2-generators.
#eval involutionMonadPushout.dimensionProfile

-- The disjointness verdict: expect `true`.
#eval computadGeneratorsDisjoint involutionMonadSplit involutionMonadPushout

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the witness pushout of two DECIDED walkers SHIPS and COMPUTES.**  The involution + monad
`ModeComputad` presentations, their concrete pushout `involutionMonadPushout` (profile `(1, 2, 2)`), the block
decomposition of the alternating word `s t s t t` into its four maximal same-component blocks (`witnessWordDecompose`,
by `rfl`), the three NF invariants at the witness word, and the disjoint-generator precondition holding by `rfl`
(`involutionMonadPushout_disjoint`).  Non-vacuous: `blockDecompose` reduces on concrete data.  `= true`. -/
def fxAmalg_hasWitnessPushout : Bool := true

end FX1Poly.Polygraph.Amalgam
