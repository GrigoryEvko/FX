import LeanFX2.HoTT.Path.Inverse

/-! # HoTT/Path/Groupoid — paths form a strict groupoid

Combining `Path.trans` (composition) and `Path.symm` (inversion)
gives a strict groupoid structure at h-set:

* Composition is associative.
* `refl` is identity for composition (left and right).
* Inverses cancel: `p . symm p = refl`, `symm p . p = refl`.
* Inverse is involutive: `symm (symm p) = p`.
* Composition respects inverses: `symm (p . q) = symm q . symm p`.

The associativity, identity, and inverse laws are proven in
`Path/Composition.lean` and `Path/Inverse.lean`.  This file
collects them as a uniform "groupoid" interface and ships
additional derived lemmas useful for downstream HoTT/HIT proofs.

## Higher coherence (∞-groupoid)

Strict groupoid laws apply at the path level (1-cells).  The
HIT layer introduces 2-paths (paths between paths) where these
laws need their own coherences (associator pentagon, inverse
hexagon, etc.).  Those 2-cell laws live in `HoTT/HIT/*` and
are deferred to v1.1+ along with higher-truncation structure.

## Dependencies

* `HoTT/Path/Composition.lean` — composition + assoc + identity
* `HoTT/Path/Inverse.lean` — inversion + involution + cancellation

## Downstream consumers

* `HoTT/HIT/*` — HITs use the groupoid structure for path ctors
* `HoTT/Equivalence.lean` — equivalences are coherent groupoid
  morphisms
-/

namespace LeanFX2

universe pathLevel

/-! ## Strict groupoid laws (collected interface) -/

/-- The eight foundational groupoid laws.  Bundled as a structure
for downstream code that wants to abstract over the carrier
type's path operations.  The `mk` constructor is filled in by
the meta-level instance below. -/
structure PathGroupoidLaws (Carrier : Sort pathLevel) : Prop where
  /-- Associativity of composition. -/
  trans_assoc :
    ∀ {endpoint0 endpoint1 endpoint2 endpoint3 : Carrier}
      (leftPath : Path endpoint0 endpoint1)
      (midPath  : Path endpoint1 endpoint2)
      (rightPath : Path endpoint2 endpoint3),
      Path.trans (Path.trans leftPath midPath) rightPath
        = Path.trans leftPath (Path.trans midPath rightPath)
  /-- Left identity for composition. -/
  trans_refl_left :
    ∀ {leftEndpoint rightEndpoint : Carrier}
      (somePath : Path leftEndpoint rightEndpoint),
      Path.trans (Path.refl leftEndpoint) somePath = somePath
  /-- Right identity for composition. -/
  trans_refl_right :
    ∀ {leftEndpoint rightEndpoint : Carrier}
      (somePath : Path leftEndpoint rightEndpoint),
      Path.trans somePath (Path.refl rightEndpoint) = somePath
  /-- Inversion is involutive. -/
  symm_symm :
    ∀ {leftEndpoint rightEndpoint : Carrier}
      (somePath : Path leftEndpoint rightEndpoint),
      Path.symm (Path.symm somePath) = somePath
  /-- Right inverse: composition followed by its inverse is reflexivity. -/
  trans_symm_right :
    ∀ {leftEndpoint rightEndpoint : Carrier}
      (somePath : Path leftEndpoint rightEndpoint),
      Path.trans somePath (Path.symm somePath)
        = Path.refl leftEndpoint
  /-- Left inverse: an inverse followed by its composition is reflexivity. -/
  trans_symm_left :
    ∀ {leftEndpoint rightEndpoint : Carrier}
      (somePath : Path leftEndpoint rightEndpoint),
      Path.trans (Path.symm somePath) somePath
        = Path.refl rightEndpoint
  /-- Inversion swaps composition order. -/
  symm_trans :
    ∀ {endpoint0 endpoint1 endpoint2 : Carrier}
      (leftPath  : Path endpoint0 endpoint1)
      (rightPath : Path endpoint1 endpoint2),
      Path.symm (Path.trans leftPath rightPath)
        = Path.trans (Path.symm rightPath) (Path.symm leftPath)
  /-- Inverting `refl` is `refl`. -/
  symm_refl :
    ∀ (someValue : Carrier),
      Path.symm (Path.refl someValue) = Path.refl someValue

/-- Every type has the strict groupoid structure on its paths
(via Lean Eq).  All 8 laws come from `Path/Composition.lean` and
`Path/Inverse.lean`. -/
def PathGroupoidLaws.instance (Carrier : Sort pathLevel) :
    PathGroupoidLaws Carrier where
  trans_assoc       := Path.trans_assoc
  trans_refl_left   := Path.trans_refl_left
  trans_refl_right  := Path.trans_refl_right
  symm_symm         := Path.symm_symm
  trans_symm_right  := Path.trans_symm_right
  trans_symm_left   := Path.trans_symm_left
  symm_trans        := Path.symm_trans
  symm_refl         := Path.symm_refl

/-! ## Derived lemmas — cancellation + move-along

The cancellation lemmas (`trans_left_cancel`, `trans_right_cancel`)
were deferred earlier because `cases commonPath` doesn't auto-
reduce `Eq.trans Eq.refl _`.  The fix: use `subst` to substitute
the variable, then path induction on the remaining path.  Both
lemmas now ship at h-set level. -/

/-- Right cancellation: if `commonPath . leftPath = commonPath .
rightPath`, then `leftPath = rightPath`.  Proof: subst the common
path's variable, then both sides reduce by definitional unfolding
of trans + refl. -/
theorem Path.trans_left_cancel {Carrier : Sort pathLevel}
    {endpoint0 endpoint1 endpoint2 : Carrier}
    (commonPath : Path endpoint0 endpoint1)
    {leftPath rightPath : Path endpoint1 endpoint2}
    (composedEq : Path.trans commonPath leftPath
                = Path.trans commonPath rightPath) :
    leftPath = rightPath := by
  subst commonPath
  exact composedEq

/-- Left cancellation: if `leftPath . commonPath = rightPath .
commonPath`, then `leftPath = rightPath`.  Mirror of right
cancellation. -/
theorem Path.trans_right_cancel {Carrier : Sort pathLevel}
    {endpoint0 endpoint1 endpoint2 : Carrier}
    (commonPath : Path endpoint1 endpoint2)
    {leftPath rightPath : Path endpoint0 endpoint1}
    (composedEq : Path.trans leftPath commonPath
                = Path.trans rightPath commonPath) :
    leftPath = rightPath := by
  subst commonPath
  -- After subst, both sides become `Path.trans X Eq.refl` which
  -- reduces to X via path induction.  The composedEq directly
  -- gives leftPath = rightPath after the cases-on-each-path
  -- collapses the trans operations.
  cases leftPath
  cases rightPath
  rfl

/-- "Move-along" lemma: if `rightPath = leftPath . midPath`, then
`symm leftPath . rightPath = midPath`.  Standard HoTT identity-
type manipulation. -/
theorem Path.trans_symm_move_left {Carrier : Sort pathLevel}
    {endpoint0 endpoint1 endpoint2 : Carrier}
    (leftPath  : Path endpoint0 endpoint1)
    (midPath   : Path endpoint1 endpoint2)
    (rightPath : Path endpoint0 endpoint2)
    (originalEq : rightPath = Path.trans leftPath midPath) :
    Path.trans (Path.symm leftPath) rightPath = midPath := by
  subst originalEq
  cases leftPath
  rfl

/-! ## Smoke samples -/

example : PathGroupoidLaws Bool := PathGroupoidLaws.instance Bool
example : PathGroupoidLaws Nat  := PathGroupoidLaws.instance Nat

/-- The associator at concrete refl paths reduces to `rfl`. -/
example :
    Path.trans (Path.trans (Path.refl (1 : Nat)) (Path.refl 1))
                (Path.refl 1)
      = Path.trans (Path.refl 1) (Path.trans (Path.refl 1) (Path.refl 1)) :=
  rfl

end LeanFX2
