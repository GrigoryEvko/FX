import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort

/-! # WalkingString/StringCapWindowColourTruthProbe — the located-prefix colour read, truth-probed FIRST
(FC-3 r24, B1)

r24's stated plan (the r23 ledger, `StringWordPairSeatedDescent`'s round ledger) was to discharge the descent
master's threaded premise

  `prefixSharesWindowMode : ∀ atom, atom ∈ prefixAtoms → atom.leftMidMode = target.leftMidMode`

from `AllCapArity` on the located pure-cap spine — "the located spine's caps sharing the toucher's window
colour".  Before assembling anything on top of that discharge, this file TRUTH-PROBES the colour read on a
concrete located-shaped spine.  The verdict comes back **FALSE**: a pure-cap prefix genuinely CAN carry a cap of
the OPPOSITE window colour to the toucher, so `prefixSharesWindowMode` is NOT derivable from `AllCapArity`.

The mechanism (P1, `adjointTripleAtom_windowPositionMode`): an atom's window colour is its `leftMidMode`, forced
by its window-position PARITY.  At the adjoint triple a cap seats at EITHER parity — `counitUpper : H·G ⇒ id_base`
seats `base`, `counitLower : G·F ⇒ id_tip` seats `tip` (unlike the single adjunction, where every cap is `tip`).
Two pairwise-disjoint caps at window positions of OPPOSITE parity are both valid pure caps in one boundary-chained
spine, so the toucher and a prefix cap can carry different colours.

  * `stringColourProbeCapUpper` — a concrete `counitUpper` cap at window `0` (`leftMidMode = base`);
  * `stringColourProbeCapLower` — a concrete `counitLower` cap at window `1` (`leftMidMode = tip`);
  * ★ `stringColourProbe_windowColoursDiffer` — the two are genuine caps (dom length `2`, cod length `0`) whose
    window colours are read off P1 as `base` and `tip` respectively — DIFFERENT;
  * ★ `stringColourProbe_dischargeInstanceFails` — the DECISIVE refutation: for the concrete
    `prefixAtoms = [stringColourProbeCapLower]`, `target = stringColourProbeCapUpper`, the discharge instance
    `∀ atom, atom ∈ prefixAtoms → atom.leftMidMode = target.leftMidMode` is FALSE (`tip ≠ base`), even though
    both caps are `AllCapArity`.

## What this settles (the r24 adjudication, honestly)

Route (a) of the r23 plan — "derive `prefixSharesWindowMode` from `AllCapArity`" — is refuted concretely here.
Route (b) — "read the prefix colours off the r20 located window certificate `StringArcPairCapWindow`" — is
independently dead: that certificate's payload (`StringArcPairCapWindow.intro`) is union-find / positional only
(split + cap arity + `ArcPairUntouched` prefix + the two ordered seed-port reads) and carries ZERO `leftMidMode`
data about the prefix atoms.

So the shipped descent master's `prefixSharesWindowMode` premise is genuinely NOT free at the adjoint triple, and
the `StringCapHeadExtractionWordPin` inhabitant is NOT delivered by "AllCapArity + composition".  The honest
unblocking route is POSITIONAL, not colour: the toucher's two legs are CONSECUTIVE untouched seed ports
(`StringArcPairCapWindow bottomCount windowPosition (windowPosition + 1)`), and a pure-cap prefix never inserts
between them (only cups do — banned), so the descent's gap-closing case is positionally excluded WITHOUT colour —
a descent-master re-founding (a later round), NOT this file.  This file ships ONLY the truth-probe and its verdict.

Raw Lean 4 + Init; the probe is `rfl` + `AdjointTripleMode.noConfusion`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two concrete located-shaped cap atoms (opposite window colours, one boundary-chained spine) -/

/-- A concrete `counitUpper` cap `ε' : H·G ⇒ id_base` at the FRONT of a `base`-source spine (left context
`id_base`, window position `0`).  Dom `H·G` (length `2`), cod `id_base` (length `0`), `leftMidMode = base`.  This
is the TOUCHER shape — a cap whose two legs are the two front seed ports. -/
def stringColourProbeCapUpper :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringHG,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    StringTwoCell.counitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩

/-- A concrete `counitLower` cap `ε : G·F ⇒ id_tip` seated at window position `1` of a `base`-source spine (left
context `F : base ⟶ tip` of length `1`, right context `G : tip ⟶ base`).  Dom `G·F` (length `2`), cod `id_tip`
(length `0`), `leftMidMode = tip`.  A genuine pure cap of the OPPOSITE window colour to `stringColourProbeCapUpper`
— a valid prefix cap in the same `base`-source spine. -/
def stringColourProbeCapLower :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.cons AdjointTripleModality.left
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip),
    stringGF,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    StringTwoCell.counitLower,
    ModalityPath.cons AdjointTripleModality.right
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)⟩

/-! ## Both are genuine pure caps -/

/-- The two-cap probe spine `[capLower, capUpper]` is pure cap (`AllCapArity`): each carries cap arity `(2, 0)`. -/
theorem stringColourProbe_bothPureCap :
    AllCapArity [stringColourProbeCapLower, stringColourProbeCapUpper] :=
  AllCapArity.cons rfl rfl (AllCapArity.cons rfl rfl AllCapArity.nil)

/-! ## The window colours, read off P1, DIFFER -/

/-- The upper cap's window colour, read off P1 (`adjointTripleAtom_windowPositionMode`): window position `0`
carries mode `base` — the toucher's `leftMidMode`. -/
theorem stringColourProbeCapUpper_windowColour :
    adjointTripleModeAtDistance AdjointTripleMode.base
        stringColourProbeCapUpper.leftContext.length
      = AdjointTripleMode.base :=
  adjointTripleAtom_windowPositionMode stringColourProbeCapUpper

/-- The lower cap's window colour, read off P1: window position `1` carries mode `tip` — the OPPOSITE of the upper
cap's colour. -/
theorem stringColourProbeCapLower_windowColour :
    adjointTripleModeAtDistance AdjointTripleMode.base
        stringColourProbeCapLower.leftContext.length
      = AdjointTripleMode.tip :=
  adjointTripleAtom_windowPositionMode stringColourProbeCapLower

/-- ★ **The two located-shaped pure caps carry DIFFERENT window colours.**  Both are genuine caps
(`stringColourProbe_bothPureCap`), yet `stringColourProbeCapUpper.leftMidMode = base` while
`stringColourProbeCapLower.leftMidMode = tip` — the concrete witness that a pure-cap prefix can host a cap of the
opposite window colour to the toucher. -/
theorem stringColourProbe_windowColoursDiffer :
    stringColourProbeCapUpper.leftMidMode ≠ stringColourProbeCapLower.leftMidMode := by
  intro coloursEqual
  exact AdjointTripleMode.noConfusion coloursEqual

/-! ## The decisive verdict — the r23-planned discharge instance is FALSE -/

/-- ★ **The colour read comes back FALSE — the located-prefix discharge is NOT derivable from `AllCapArity`.**
For the concrete `prefixAtoms = [stringColourProbeCapLower]` and `target = stringColourProbeCapUpper` — both pure
caps — the descent master's threaded premise instance
`∀ atom, atom ∈ prefixAtoms → atom.leftMidMode = target.leftMidMode` is FALSE: the single prefix cap carries
`leftMidMode = tip`, the toucher `leftMidMode = base`, and `tip ≠ base`.  This refutes route (a) of the r23 r24
plan (the "AllCapArity colour augmentation") CONCRETELY — the wall is genuine, and the honest route is positional
(the toucher's consecutive untouched legs), not colour. -/
theorem stringColourProbe_dischargeInstanceFails :
    ¬ (∀ atom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base,
        atom ∈ [stringColourProbeCapLower] →
        atom.leftMidMode = stringColourProbeCapUpper.leftMidMode) := by
  intro dischargeHolds
  have prefixColourEqualsTarget :
      stringColourProbeCapLower.leftMidMode = stringColourProbeCapUpper.leftMidMode :=
    dischargeHolds stringColourProbeCapLower (List.Mem.head [])
  exact AdjointTripleMode.noConfusion prefixColourEqualsTarget

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the located-prefix colour read, truth-probed, comes back FALSE (FC-3 r24, B1).**  The r23
r24 plan proposed to discharge the descent master's threaded `prefixSharesWindowMode` premise from `AllCapArity`
on the located pure-cap spine.  This file probes the colour read on a concrete located-shaped spine and settles it
NEGATIVELY: `stringColourProbeCapUpper` (window `0`, `leftMidMode = base`) and `stringColourProbeCapLower`
(window `1`, `leftMidMode = tip`) are BOTH genuine pure caps (`stringColourProbe_bothPureCap`) whose window
colours, read off P1 (`adjointTripleAtom_windowPositionMode`), DIFFER (`stringColourProbe_windowColoursDiffer`);
hence the discharge instance `∀ atom ∈ [capLower], atom.leftMidMode = capUpper.leftMidMode` is FALSE
(`stringColourProbe_dischargeInstanceFails`).

  THE ADJUDICATION.  Route (a) — "`AllCapArity` ⟹ `prefixSharesWindowMode`" — is refuted concretely here.
  Route (b) — "read the prefix colours off the r20 `StringArcPairCapWindow` located certificate" — is dead
  independently: that certificate's payload is union-find / positional only (split + cap arity + `ArcPairUntouched`
  prefix + two ordered seed-port reads), carrying ZERO prefix `leftMidMode` data.  So `StringCapHeadExtractionWordPin`
  is NOT delivered by "AllCapArity + composition" this round, and no unconditional cap sort flips.  The honest
  unblocking route is POSITIONAL: the toucher's two legs are consecutive untouched seed ports and a pure-cap prefix
  never inserts between them, so the descent's gap-closing case is positionally excluded WITHOUT colour — a
  descent-master re-founding, the named r24 residual, not this file.  `= true`. -/
def fxString_hasCapWindowColourTruthProbe : Bool := true

end FX1Poly.Polygraph
