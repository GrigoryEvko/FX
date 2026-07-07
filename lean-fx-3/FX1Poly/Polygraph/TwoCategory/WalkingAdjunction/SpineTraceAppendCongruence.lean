import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend

/-! # WalkingAdjunction/SpineTraceAppendCongruence — the two-sided append congruence of trace equivalence

The shipped `spineTraceEquiv_backAppendCongr` appends a single fixed trailing ATOM to both sides of a
`SpineTraceEquiv`.  The fib-3 keystone's existence route needs the block-combination step of piece (II): a
valley `V = capBlock ++ cupBlock`, so combining `SpineTraceEquiv capBlock1 capBlock2` and
`SpineTraceEquiv cupBlock1 cupBlock2` into `SpineTraceEquiv (capBlock1 ++ cupBlock1) (capBlock2 ++ cupBlock2)`
requires appending and prepending whole LISTS, not single atoms.  This file ships exactly that:

  * ★ `atomicTraceEquiv_backAppendListCongr` — the list-suffix generalization of the shipped
    single-atom `atomicTraceEquiv_backAppendCongr`.  Each adjacent swap's trailing `rest` absorbs the whole
    appended suffix (`(a :: b :: rest) ++ suffix` reduces definitionally to `a :: b :: (rest ++ suffix)`),
    so the `ofSwap` case re-applies the `swap` constructor at `rest ++ suffix` — the same one-line move as the
    shipped proof, with `[tailAtom]` replaced by `suffix`.  No `List.append_assoc` (which would leak
    `propext`); the reduction is purely `List.cons_append` (`rfl`).
  * ★ `spineTraceEquiv_backAppendListCongr` — its block-level image via `spineTraceEquiv_iff_atomicTraceEquiv`.
  * ★ `spineTraceEquiv_prefixListCongr` — a fixed list PREFIX passes through both sides, by iterating the
    head-cons congruence `SpineTraceEquiv.consCongr` down the prefix (`headAtom :: restPrefix ++ tail` reduces
    to `headAtom :: (restPrefix ++ tail)` definitionally).
  * ★ `spineTraceEquiv_appendCongr` — the two-sided combination: `A ~ B` and `C ~ D` give `A ++ C ~ B ++ D`,
    glued `A ++ C ~ B ++ C ~ B ++ D` (suffix congruence then prefix congruence, one `trans`).

Raw Lean 4 + Init; the suffix congruence is a structural induction on the atomic closure with the swap's
`rest` extended, the prefix congruence a structural recursion on the prefix list, the combination a single
`trans`.  No `List.append_assoc`, no `omega`, no `simp`-AC.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **List back-append congruence for the ATOMIC trace equivalence.**  Appending a fixed trailing list
`suffix` to both sides of an `AtomicTraceEquiv` preserves it.  Each adjacent swap's trailing tail `rest`
absorbs the whole appended suffix — `(a :: b :: rest) ++ suffix` reduces definitionally (twice `List.cons_append`)
to `a :: b :: (rest ++ suffix)` — so the `ofSwap` case re-applies the `swap` constructor at `rest ++ suffix`;
`refl` / `symm` / `trans` / `consCongr` thread the appended tail congruence arm for arm.  The list-suffix
generalization of the shipped single-atom `atomicTraceEquiv_backAppendCongr`. -/
theorem atomicTraceEquiv_backAppendListCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList)
    (suffix : List (SpineAtom signature overallSource overallTarget)) :
    AtomicTraceEquiv signature (firstList ++ suffix) (secondList ++ suffix) := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
          oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
          rightAcc rest =>
          exact AtomicTraceEquiv.ofSwap
            (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc
              (rest ++ suffix))
  | refl spineList => exact AtomicTraceEquiv.refl (spineList ++ suffix)
  | symm _ innerHypothesis => exact AtomicTraceEquiv.symm innerHypothesis
  | trans _ _ leftHypothesis rightHypothesis => exact leftHypothesis.trans rightHypothesis
  | consCongr atom _ innerHypothesis => exact AtomicTraceEquiv.consCongr atom innerHypothesis

/-- ★ **List back-append congruence for the block-level trace equivalence.**  Appending a fixed trailing list
`suffix` to both sides of a `SpineTraceEquiv` preserves it.  Routed through the atom granularity
(`spineTraceEquiv_iff_atomicTraceEquiv`), the atomic list-back-append absorbs the whole suffix, and the result
maps back to the block level. -/
theorem spineTraceEquiv_backAppendListCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList)
    (suffix : List (SpineAtom signature overallSource overallTarget)) :
    SpineTraceEquiv signature (firstList ++ suffix) (secondList ++ suffix) :=
  spineTraceEquiv_iff_atomicTraceEquiv.mpr
    (atomicTraceEquiv_backAppendListCongr
      (spineTraceEquiv_iff_atomicTraceEquiv.mp equiv) suffix)

/-- ★ **List prefix congruence for the block-level trace equivalence.**  Prepending a fixed list `prefixList`
to both sides of a `SpineTraceEquiv` preserves it, by iterating the head-cons congruence
`SpineTraceEquiv.consCongr` down the prefix.  `(headAtom :: restPrefix) ++ tail` reduces definitionally to
`headAtom :: (restPrefix ++ tail)`, so the recursion re-seats one head atom per step. -/
theorem spineTraceEquiv_prefixListCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
    (prefixList : List (SpineAtom signature overallSource overallTarget)) →
    SpineTraceEquiv signature firstList secondList →
    SpineTraceEquiv signature (prefixList ++ firstList) (prefixList ++ secondList)
  | [], equiv => equiv
  | headAtom :: restPrefix, equiv =>
      SpineTraceEquiv.consCongr headAtom (spineTraceEquiv_prefixListCongr restPrefix equiv)

/-- ★ **The two-sided append congruence of the trace equivalence.**  Trace-equivalent prefixes and
trace-equivalent suffixes append to trace-equivalent concatenations: `A ~ B` and `C ~ D` give `A ++ C ~ B ++ D`.
Glued `A ++ C ~ B ++ C ~ B ++ D` — the suffix congruence (fixed suffix `C`, varying prefix `A ~ B`) then the
prefix congruence (fixed prefix `B`, varying suffix `C ~ D`) — in one `trans`.  This is the block-combination
step the fib-3 existence route's piece (II) needs: a valley is `capBlock ++ cupBlock`, and the two pure-block
sorts combine through exactly this congruence. -/
theorem spineTraceEquiv_appendCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstPrefix secondPrefix firstSuffix secondSuffix :
      List (SpineAtom signature overallSource overallTarget)}
    (prefixEquiv : SpineTraceEquiv signature firstPrefix secondPrefix)
    (suffixEquiv : SpineTraceEquiv signature firstSuffix secondSuffix) :
    SpineTraceEquiv signature (firstPrefix ++ firstSuffix) (secondPrefix ++ secondSuffix) :=
  SpineTraceEquiv.trans
    (spineTraceEquiv_backAppendListCongr prefixEquiv firstSuffix)
    (spineTraceEquiv_prefixListCongr secondPrefix suffixEquiv)

/-! ## Honesty marker -/

/-- **Honesty marker — the two-sided append congruence of the trace equivalence is SHIPPED.**  The list-suffix
back-append `atomicTraceEquiv_backAppendListCongr` / `spineTraceEquiv_backAppendListCongr` generalizes the
shipped single-atom version (the swap's `rest` absorbs a whole list, `propext`-free — pure `List.cons_append`),
the list-prefix congruence `spineTraceEquiv_prefixListCongr` iterates `consCongr`, and
`spineTraceEquiv_appendCongr` combines them into `A ~ B → C ~ D → A ++ C ~ B ++ D` with one `trans`.  This is
the block-combination step of the fib-3 existence route's piece (II): a valley `V = capBlock ++ cupBlock`, so
the two pure-block sorts (`pureCapSpine_sort`, `pureCupSpine_sort`) join through this congruence.  What this
marker does NOT claim: the valley split or the pure-block arc-from-matching bridge (the finer/coarser residual);
only the append plumbing that consumes them.  `= true`. -/
def fxMode_hasSpineTraceAppendCongruence : Bool := true

end FX1Poly.Polygraph
