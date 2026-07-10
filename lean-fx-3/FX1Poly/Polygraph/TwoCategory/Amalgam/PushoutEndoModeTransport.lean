import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallBlockScaffold

/-! # Polygraph/TwoCategory/Amalgam/PushoutEndoModeTransport — the endo-`ModalityPath`-at-single-mode TRANSPORT:
the keystone that unlocks the wall-free 1-cell converse and the cell-carrying finest layout (WP-AMALG-2 r11, B1)

The r10 ledger (`PushoutWallFreeInversionLedger.lean`) factorized the residual to five precisely-named nodes and
found the two NEAREST (`pathInvert`, `finestLayout`) "both blocked ONLY on the single-mode intermediate-mode
transport": a per-letter reconstruction needs each intermediate mode typed `monadPushMode`, but a `ModalityPath`
`cons`'s middle mode is provably-but-not-syntactically the single mode.  This file authors that transport.

## The singleton fact and its consequence: every pushout generator is an ENDO

`involutionMonadPushout.modeCount = 1` (both components contribute the one shared mode), so `Fin
involutionMonadPushout.modeCount` is a SINGLETON: `pushoutModeUnique` proves every mode `= monadPushMode`, by the
`Fin.mk`-casing / `Nat.not_lt_zero` route (propext-free, the technique already live inside `reseatGen`).  Its
consequence is the load-bearing structural fact: `pushoutGenEndpoints` — EVERY pushout 1-generator has recorded
endpoints `(monadPushMode, monadPushMode)` (both projections coerced by the singleton), so every pushout letter is
an endo at the single mode.

## The transport: word ⟷ endo path, a bijection

Because every letter is an endo, `pushoutEndoPathOfWord` builds an endo `ModalityPath` at `monadPushMode` from ANY
boundary word (each index tagged endo by `pushoutGenEndpoints`) — the middle mode VANISHES (the output type is
fixed endo, so no `Eq.rec`-through-a-type-level-function ever arises).  The two round-trips make it a bijection with
`pushoutPathWord`:

  * **`pushoutPathWord_pushoutEndoPathOfWord`** — `pushoutPathWord ∘ pushoutEndoPathOfWord = id` (structural
    `congrArg`, the letter's `.val` is exactly the index).
  * **`pushoutPathWord_injective`** — a pushout 1-cell is DETERMINED by its boundary word.  The single dependent
    `cons` reconstruction: the shared middle mode is pinned by the head letter's recorded endpoints
    (`letter.property`, a `Prod.snd` `congrArg`), `subst`d (RAW pushout cons indices are variables — clean), the
    two letters identified by `Subtype.ext`.  A direct port of the shipped `monadPathWord_injective`, dodging the
    childCons injection-drilling landmine on the function-application-indexed mapped `cons`.
  * **`pushoutEndoPathOfWord_pushoutPathWord`** — `pushoutEndoPathOfWord ∘ pushoutPathWord = id` on endo paths, via
    the injectivity (the transport round-trips both ways).

This is the endo-`ModalityPath`-at-single-mode transport the r10 ledger named.  The word route (Lists carry no
mode index) makes the transport a total structural fold; the singleton enters ONLY through `pushoutGenEndpoints`,
never hand-rolled through a type-level function.

## The wall-free hypothesis and the negative control (self-attack)

`pathWallFree` is the per-letter component-2 (`letterTag = false`) predicate — the hypothesis the MONAD-side
reconstruction (`pathInvert`, B2) is gated by.  The negative control confirms the gate is real:
`monadPushSPath_notWallFree` proves the `s`-wall path does NOT satisfy it (its head letter tags `true`).  The
transport itself (`pushoutEndoPathOfWord`) is UNCONDITIONAL — it re-types any word as an endo pushout path; the
wall-free hypothesis discriminates only which endo paths further descend to the monad component.

## What STAYS WALLED (no flip)

This ships the transport + the singleton + the reflection + the wall-free hypothesis — NOT the MONAD-side
`pathInvert` (B2) nor the cell-carrying `finestLayout` (B3) nor `wallFreeCellInvert`.  Those are the downstream
nodes standing on this transport.  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS
`false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the word / path.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The singleton fact -/

/-- ★★ **THE SINGLETON FACT** — every mode of the `involution +_M monad` pushout is `monadPushMode`.  The pushout
carries `modeCount = 1` (both components share the one mode), so `Fin involutionMonadPushout.modeCount` is a
singleton: an index `⟨0, _⟩` is `monadPushMode` by `Fin`-proof-irrelevance (`rfl`), and any `⟨count + 1, _⟩` is
absurd (`Nat.not_lt_zero`).  Propext-free (`Fin.mk` casing, NOT `Fin.cases`).  This is the "provably-but-not-
syntactically the single mode" fact the r10 ledger named, now a reusable coercion. -/
theorem pushoutModeUnique (mode : Fin involutionMonadPushout.modeCount) : mode = monadPushMode :=
  match mode with
  | ⟨0, _⟩ => rfl
  | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-- ★ **Every pushout 1-generator is an ENDO** at the single mode — its recorded endpoints are
`(monadPushMode, monadPushMode)`, both projections coerced by the singleton `pushoutModeUnique`.  This is the
structural consequence that lets the transport re-type ANY word as an endo path (a `Prod`-eta step through the two
singleton coercions — no `decide` on a `Prod`-of-`Fin` equality, which would pull `propext`). -/
theorem pushoutGenEndpoints (index : Fin involutionMonadPushout.modalityGenerators.length) :
    involutionMonadPushout.modalityGenerators.get index = (monadPushMode, monadPushMode) := by
  have leftEndpoint := pushoutModeUnique (involutionMonadPushout.modalityGenerators.get index).1
  have rightEndpoint := pushoutModeUnique (involutionMonadPushout.modalityGenerators.get index).2
  calc involutionMonadPushout.modalityGenerators.get index
      = ((involutionMonadPushout.modalityGenerators.get index).1,
         (involutionMonadPushout.modalityGenerators.get index).2) := rfl
    _ = (monadPushMode, monadPushMode) := by rw [leftEndpoint, rightEndpoint]

/-! ## The transport: word ⟶ endo path -/

/-- ★★★ **THE TRANSPORT.**  Build an endo `ModalityPath` at `monadPushMode` from an arbitrary boundary word: each
index is tagged endo by `pushoutGenEndpoints`, so the middle mode VANISHES (the output type is fixed endo, never
threaded through a type-level function).  Structural on the word; the empty word is the identity path.  This is the
endo-`ModalityPath`-at-single-mode transport the r10 ledger blocked on — total, `Eq.rec`-free. -/
def pushoutEndoPathOfWord :
    List (Fin involutionMonadPushout.modalityGenerators.length) →
    ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode
  | [] => ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  | index :: rest =>
      ModalityPath.cons
        (⟨index, pushoutGenEndpoints index⟩ : involutionMonadPushout.Modality monadPushMode monadPushMode)
        (pushoutEndoPathOfWord rest)

/-- ★ **`pushoutPathWord ∘ pushoutEndoPathOfWord = id`** — reading the boundary word of a transported path recovers
the word (each rebuilt letter's `.val` is exactly its index).  Structural `congrArg` on the word. -/
theorem pushoutPathWord_pushoutEndoPathOfWord :
    (word : List (Fin involutionMonadPushout.modalityGenerators.length)) →
    pushoutPathWord (pushoutEndoPathOfWord word) = word
  | [] => rfl
  | index :: rest => congrArg (index :: ·) (pushoutPathWord_pushoutEndoPathOfWord rest)

/-! ## The reflection: a pushout 1-cell is determined by its boundary word -/

/-- ★★ **`pushoutPathWord` is INJECTIVE** — a pushout 1-cell is determined by its boundary word.  Structural on the
two paths: `nil`/`cons` mismatches contradict via `List.noConfusion`; the `cons`/`cons` case `injection`s the
(non-dependent) `List` word equality into head-index and tail-word equalities, pins the shared middle mode from the
head letter's recorded endpoints (`letter.property`, a `Prod.snd` `congrArg`), `subst`s it (RAW pushout cons
indices are variables — clean), identifies the two head letters by `Subtype.ext`, and recurses on the tail.  A
direct port of the shipped `monadPathWord_injective` — dodging the childCons injection-drilling landmine.
Propext-free. -/
theorem pushoutPathWord_injective :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    (pathA pathB : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) →
    pushoutPathWord pathA = pushoutPathWord pathB → pathA = pathB
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .nil _, .cons _ _, equalWords => Nat.noConfusion (congrArg List.length equalWords)
  | _, _, .cons _ _, .nil _, equalWords => Nat.noConfusion (congrArg List.length equalWords)
  | _, _, @ModalityPath.cons _ _ middleA _ letterA restA,
          @ModalityPath.cons _ _ middleB _ letterB restB, equalWords => by
      injection equalWords with headValEqual tailWordEqual
      have middleEqual : middleA = middleB := by
        have getEqual : involutionMonadPushout.modalityGenerators.get letterA.val
            = involutionMonadPushout.modalityGenerators.get letterB.val :=
          congrArg (involutionMonadPushout.modalityGenerators.get ·) headValEqual
        exact congrArg Prod.snd (letterA.property.symm.trans (getEqual.trans letterB.property))
      subst middleEqual
      have letterEqual : letterA = letterB := Subtype.ext headValEqual
      subst letterEqual
      have restEqual : restA = restB := pushoutPathWord_injective restA restB tailWordEqual
      subst restEqual
      rfl

/-- ★★ **`pushoutEndoPathOfWord ∘ pushoutPathWord = id`** on endo paths — the transport round-trips BOTH ways.  The
word round-trip (`pushoutPathWord_pushoutEndoPathOfWord`) plus the reflection (`pushoutPathWord_injective`) recover
the path from its transported-then-read word. -/
theorem pushoutEndoPathOfWord_pushoutPathWord
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    pushoutEndoPathOfWord (pushoutPathWord path) = path :=
  pushoutPathWord_injective (pushoutEndoPathOfWord (pushoutPathWord path)) path
    (pushoutPathWord_pushoutEndoPathOfWord (pushoutPathWord path))

/-! ## The wall-free hypothesis -/

/-- The **wall-free predicate** — every letter of a pushout 1-cell is component-2 (`letterTag = false`, a `t`-gap).
Structural on the path (the empty path is vacuously wall-free).  This is the hypothesis the MONAD-side
reconstruction `pathInvert` (B2) is gated by: only wall-free pushout 1-cells descend to the monad component. -/
def pathWallFree : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode → Prop
  | _, _, .nil _ => True
  | _, _, .cons letter rest => letterTag involutionMonadSplit letter.val = false ∧ pathWallFree rest

/-! ## The truth-probe (FIRST) and the negative control (self-attack) -/

-- The concrete two-letter endo path `t·t` transports from its word `[t, t]` back to `t·t` (by defeq).
-- Its boundary word reads `[1, 1]` (both `t`-gaps at index 1). Expect `[1, 1]`.
#eval (pushoutPathWord (composePath monadPushTPath monadPushTPath)).map Fin.val

/-- ★★★ **THE TRANSPORT TRUTH-PROBE.**  A concrete two-letter endo monad path `t·t` (`composePath monadPushTPath
monadPushTPath`) is exactly what the transport rebuilds from its boundary word `[t, t]` — by DEFEQ (`rfl`, the
rebuilt letters' `.val`s are `t`, `t` and `Fin`-proof-irrelevance identifies the endpoint witnesses).  A genuine
reduction on concrete data: the transport is not vacuous. -/
theorem endoTransport_twoLetterProbe :
    pushoutEndoPathOfWord [tLetter, tLetter] = composePath monadPushTPath monadPushTPath := rfl

/-- ★★ **The wall-free predicate holds on the gap path `t`** — its one letter tags component-2 (`decide`). -/
theorem monadPushTPath_wallFree : pathWallFree monadPushTPath :=
  ⟨by decide, True.intro⟩

/-- ★★★ **THE NEGATIVE CONTROL (self-attack).**  The `s`-WALL path `monadPushSPath` does NOT satisfy the wall-free
hypothesis — its head letter tags component-1 (`letterTag involutionMonadSplit sLetter = true`, `decide`), so
`pathWallFree` fails at the first conjunct (`true ≠ false`, `Bool.noConfusion`).  This confirms the gate is real:
the transport re-types any word as an endo path, but the MONAD-side descent (`pathInvert`, B2) is correctly
inapplicable to a wall-bearing path — exactly at the `letterTag` bit. -/
theorem monadPushSPath_notWallFree : ¬ pathWallFree monadPushSPath := by
  intro wallFreeHyp
  exact Bool.noConfusion
    (wallFreeHyp.1.symm.trans (by decide : letterTag involutionMonadSplit sLetter = true))

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the endo-`ModalityPath`-at-single-mode TRANSPORT SHIPS (WP-AMALG-2 r11, B1, the
keystone).**  `= true`: the singleton fact (`pushoutModeUnique`: every pushout mode `= monadPushMode`) and its
consequence (`pushoutGenEndpoints`: every 1-generator is an endo), the transport `pushoutEndoPathOfWord` (word ⟶
endo path, the middle mode vanishing so no `Eq.rec`-through-a-type-level-function arises), its two round-trips
(`pushoutPathWord_pushoutEndoPathOfWord` + the reflection `pushoutPathWord_injective` — the direct port of
`monadPathWord_injective` dodging the childCons drilling landmine — giving `pushoutEndoPathOfWord_pushoutPathWord`),
the wall-free hypothesis (`pathWallFree`), the concrete two-letter TRUTH-PROBE (`endoTransport_twoLetterProbe`, the
transport rebuilds `t·t` from `[t, t]` by defeq), and the NEGATIVE CONTROL (`monadPushSPath_notWallFree`: the
`s`-wall path fails the wall-free gate — a genuine self-attack).  This is the single next clean lemma the r10
ledger said unlocks the two nearest nodes (`pathInvert`, `finestLayout`).  It is NOT those nodes.  No marker flips.
`= true`. -/
def fxAmalg_hasEndoModeTransport : Bool := true

end FX1Poly.Polygraph.Amalgam
