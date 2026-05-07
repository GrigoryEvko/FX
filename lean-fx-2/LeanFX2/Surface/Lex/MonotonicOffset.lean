import LeanFX2.Surface.Lex
import LeanFX2.Surface.Lex.ByteConservation

/-! # Surface/Lex/MonotonicOffset — L04 monotonic offset chain

Closes the L04 (#1202) preservation chain: the `PositionedToken`
array produced by `Lex.run` has weakly-monotonically-increasing
`startPos.offset` across token indices.

* L04.1 (#1538): predicate `Array.isMonotonicByOffset` (this file)
* L04.2 (#1539): structural preservation under `Array.push`
* L04.3 (#1540): `lexLoop_preserves_monotonic_offsets` invariant
* L04.4 (#1541): `Lex.run_offsets_monotonic` (closes L04 / #1202)

This commit ships L04.1 (the predicate definition) plus L04.2's
push-preservation auxiliary.  The `lexLoop`-induction proof
(L04.3) and `Lex.run` specialization (L04.4) land in follow-ups
to keep each commit independently auditable.

## Why `List`-based (not `Array.size`-indexed)

Stdlib `Array.size_push` depends on `List.length_concat` which
depends on `propext`.  Any quantified-pairwise predicate over
`arr.size`-bounded indices ends up rewriting through that chain
and fails strict zero-axiom audits.  The project's existing
L07.5 pattern (e.g. `Array.push_toList_mem_decompose`) instead
operates on `arr.toList`, where `(arr.push x).toList =
arr.toList.concat x` reduces by `rfl`.  We follow the same
pattern: define monotonicity as an inductive `Prop` on `List
PositionedToken`, then bridge to arrays via `Array.toList`.

## Why weak (`≤`) instead of strict (`<`)

Strict monotonicity would require proving `bytes ≥ 1` at every
emitting branch of `lexOne`, which depends on
`Char.utf8Size_pos` from stdlib.  The stdlib proof uses
`iteInduction`/`decide` over `UInt32.le_iff_toNat_le`, both of
which risk leaking `propext` through Lean 4's match compiler in
strict zero-axiom builds.

Weak monotonicity (`≤`) reflects the structural property that
offsets never decrease.  For the L04 spec ("monotonically
increasing"), this is the load-bearing claim — strict can be
added incrementally once a propext-clean `utf8Size_pos`
substitute lands.

Zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

namespace Lex

/-- **L04.1 (#1538) — list monotonicity predicate**: a list of
`PositionedToken`s is *monotonic by offset* iff every adjacent
pair has non-decreasing `startPos.offset`.

The inductive structure makes the empty / singleton / cons cases
explicit, which lets the push-preservation proof (L04.2) recurse
structurally without invoking stdlib `Array.size`/`length_concat`
machinery (both depend on `propext`). -/
inductive List.IsMonotonicByOffset : List PositionedToken → Prop
  | empty : List.IsMonotonicByOffset []
  | single (token : PositionedToken) : List.IsMonotonicByOffset [token]
  | cons
      (token1 token2 : PositionedToken)
      (restTokens : List PositionedToken)
      (hOrder : token1.startPos.offset ≤ token2.startPos.offset)
      (hRest : List.IsMonotonicByOffset (token2 :: restTokens)) :
      List.IsMonotonicByOffset (token1 :: token2 :: restTokens)

/-- **L04.1 (#1538) — array projection**: a `PositionedToken`
array is monotonic by offset iff its `toList` projection is. -/
def Array.isMonotonicByOffset (tokenArr : Array PositionedToken) : Prop :=
  List.IsMonotonicByOffset tokenArr.toList

/-! ## L04.2 (#1539) — concat preservation

The structural induction over a `List PositionedToken`
classifies into three cases, mirroring the
`List.IsMonotonicByOffset` constructor structure:

* **empty**: `[].concat lastToken = [lastToken]`, which is
  `single`.

* **single**: `[firstToken].concat lastToken = [firstToken,
  lastToken]`.  Use `cons` with the order witness from
  `hAllBelow firstToken (List.Mem.head _)`.

* **cons of cons**: `(t1 :: t2 :: rest).concat lastToken =
  t1 :: t2 :: (rest.concat lastToken)`.  The outer `cons` carries
  forward `t1 ≤ t2` from the input invariant; the inner
  monotonicity comes from recursion on `t2 :: rest`.
-/

/-- **Auxiliary**: membership in a `List.cons` decomposes into
`= head` or `∈ tail`.  Pure structural pattern match; no stdlib
`List.mem_cons` (which leaks `propext` via match-compiler). -/
theorem List.mem_cons_decompose
    {alpha : Type} {targetElem headElem : alpha}
    {tailList : List alpha}
    (hMem : targetElem ∈ headElem :: tailList) :
    targetElem = headElem ∨ targetElem ∈ tailList := by
  cases hMem with
  | head _ => exact Or.inl rfl
  | tail _ hMemTail => exact Or.inr hMemTail

/-- **L04.2 (#1539) — concat preservation**: if `initialList`
is monotonic and every existing token's offset is bounded by
`lastToken.startPos.offset`, then `initialList.concat lastToken`
is also monotonic.

Pure structural recursion over `initialList`; no stdlib
`Array.size` / `List.length_concat` references. -/
theorem List.IsMonotonicByOffset.concat :
    ∀ (initialList : List PositionedToken) (lastToken : PositionedToken),
      List.IsMonotonicByOffset initialList →
      (∀ pastTok ∈ initialList,
          pastTok.startPos.offset ≤ lastToken.startPos.offset) →
      List.IsMonotonicByOffset (initialList.concat lastToken)
  | [], lastToken, _hMonotonic, _hAllBelow =>
    -- `[].concat lastToken` reduces to `[lastToken]` by definition.
    List.IsMonotonicByOffset.single lastToken
  | [firstToken], lastToken, _hMonotonic, hAllBelow =>
    -- `[firstToken].concat lastToken` reduces to `[firstToken, lastToken]`.
    List.IsMonotonicByOffset.cons firstToken lastToken []
      (hAllBelow firstToken (List.Mem.head []))
      (List.IsMonotonicByOffset.single lastToken)
  | firstToken :: secondToken :: restTokens, lastToken,
    hMonotonic, hAllBelow => by
    -- `(t1 :: t2 :: rest).concat lastToken` reduces to
    -- `t1 :: t2 :: (rest.concat lastToken)`.  Outer cons retains
    -- `t1 ≤ t2`; inner monotonicity by recursion on `t2 :: rest`.
    cases hMonotonic with
    | cons _ _ _ hOrder hRestMonotonic =>
      -- Build the recursive monotonicity at `(secondToken ::
      -- restTokens).concat lastToken`.  Definitionally equal to
      -- `secondToken :: restTokens.concat lastToken`.
      have hRecur :
          List.IsMonotonicByOffset
            ((secondToken :: restTokens).concat lastToken) :=
        List.IsMonotonicByOffset.concat
          (secondToken :: restTokens) lastToken hRestMonotonic
          (fun pastTok pastMember =>
            hAllBelow pastTok (List.Mem.tail firstToken pastMember))
      -- The inductive cons constructor reassembles outer pair.
      exact List.IsMonotonicByOffset.cons firstToken secondToken
        (restTokens.concat lastToken) hOrder hRecur

/-- **L04.2 (#1539) — array push preservation**: if `arrInput`
is monotonic by offset and every existing token's offset is
bounded by `newToken.startPos.offset`, then `arrInput.push
newToken` is also monotonic.

Bridge from list-level concat preservation via the `rfl`-equal
`(arr.push x).toList = arr.toList.concat x`. -/
theorem Array.isMonotonicByOffset_push
    (arrInput : Array PositionedToken) (newToken : PositionedToken)
    (hMonotonic : Array.isMonotonicByOffset arrInput)
    (hAllBelow :
      ∀ pastTok ∈ arrInput.toList,
        pastTok.startPos.offset ≤ newToken.startPos.offset) :
    Array.isMonotonicByOffset (arrInput.push newToken) :=
  -- `(arrInput.push newToken).toList = arrInput.toList.concat newToken`
  -- holds by `rfl`, so we can invoke the list-level theorem
  -- directly.  Definitional unfolding of `Array.isMonotonicByOffset`
  -- happens automatically.
  List.IsMonotonicByOffset.concat arrInput.toList newToken
    hMonotonic hAllBelow

end Lex

end LeanFX2.Surface
