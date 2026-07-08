import FX1Poly.Polygraph.Computad.Signature

/-! # WalkingInvolution/InvolutionSeed — the walking-involution seed: one 1-generator with a strict `s.s = id` relation

The presentation of the WALKING INVOLUTION as a mode theory: ONE mode `point`, ONE endo-1-generator
`s : point ⟶ point`, and the strict relation `s.s = id` at the 1-CELL level (the involution law).  There are NO
generating 2-cells — the 2-signature is FREE ON NOTHING (`twoCell := fun _ _ => Empty`), so 2-cell equality is
exactly 1-cell equality and the whole word problem lives one dimension DOWN from the walking monad's.

## The involution is the mode theory of session duality

By Wadler ("Propositions as Sessions", JFP 2014) session-type DUALITY is a strict involution: `dual(dual(S)) = S`
(equivalently `(A⊥)⊥ = A` in classical linear logic).  FX's `fx_design.md` §11.2 posits exactly this table —
`dual(send(T).S) = receive(T).dual(S)`, `dual(receive(T).S) = send(T).dual(S)`, `dual(S1 + S2) = dual(S1) & dual(S2)`,
`dual(end) = end` — with `dual(dual(P)) = P`.  The walking involution `⟨s | s.s = id⟩` is the terminal such theory:
`s` is `dual`, and a chain of `dual`s composes to `id` (even parity) or a single `dual` (odd parity).

## What is shipped here (each piece zero-axiom)

  * **`InvolutionMode` / `InvolutionModality`** — one 0-cell `point`, one endo-1-generator `s`.
  * **`involutionGraph`** — the walking-involution quiver.
  * **`involutionS`** — the generator `s` as the length-1 free 1-cell.
  * **`involutionModeSignature`** — the degenerate 2-computad: the same quiver with NO generating 2-cells
    (`twoCell := fun _ _ => Empty`), witnessing "2-cells are only identities".

The `s.s = id` relation itself is the 1-cell CONVERTIBILITY `InvolutionOneCellConv` (a sibling of the walking
monad's saturated 2-cell `MonadSaturatedTwoCellConv`, one dimension down); the model / soundness / completeness /
decision follow in `InvolutionParity` and `InvolutionDecision`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The walking-involution quiver: one object, one endo-generator -/

/-- The single mode (0-cell) of the walking involution. -/
inductive InvolutionMode where
  /-- The unique object. -/
  | point

/-- The single generating modality (1-cell) of the walking involution: the endo-generator `s : point ⟶ point`
(the DUAL of session-type duality). -/
inductive InvolutionModality : InvolutionMode → InvolutionMode → Type where
  /-- The generating endo-1-cell `s`. -/
  | s : InvolutionModality InvolutionMode.point InvolutionMode.point

/-- The walking-involution quiver: one mode, one endo-modality. -/
def involutionGraph : ModeGraph where
  Mode := InvolutionMode
  Modality := InvolutionModality

/-- The identity 1-cell at `point` (the empty word — the RHS of the involution law `s.s = id`).  Names the
`graph`-annotated `nil` so downstream sites need not re-annotate the implicit `ModeGraph`. -/
def involutionNil : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point :=
  ModalityPath.nil (graph := involutionGraph) InvolutionMode.point

/-- The generating endo-1-cell `s` as the length-1 free 1-cell (the single-step path). -/
def involutionS : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point :=
  singletonModalityPath InvolutionModality.s

/-- ★ The **walking-involution mode signature** — the degenerate 2-computad: the involution quiver with NO
generating 2-cells (`twoCell` is `Empty` on every parallel pair).  The involution's only relation lives at the
1-cell level (`s.s = id`, the `InvolutionOneCellConv` in `InvolutionParity`); at the 2-cell level the signature is
FREE ON NOTHING, so every 2-cell is an identity and 2-cell equality collapses to 1-cell equality. -/
def involutionModeSignature : ModeSignature where
  graph := involutionGraph
  twoCell := fun _ _ => Empty

/-! ## Freeness / degeneracy smokes -/

/-- Smoke: `s` is the length-1 1-cell. -/
theorem involutionS_length : involutionS.length = 1 := rfl

/-- Smoke: `s.s` (the involution relation's left-hand side) is the length-2 1-cell. -/
theorem involutionSThenS_length :
    (ModalityPath.cons InvolutionModality.s involutionS).length = 2 := rfl

/-- Smoke: the 2-signature is FREE ON NOTHING — there is no generating 2-cell between any parallel pair (here
`s ⇒ s`), so 2-cell equality is 1-cell equality.  Witnessed by the emptiness of the `twoCell` family. -/
theorem involution_no_two_generators
    (generatingTwoCell : involutionModeSignature.twoCell involutionS involutionS) : False :=
  nomatch generatingTwoCell

end FX1Poly.Polygraph
