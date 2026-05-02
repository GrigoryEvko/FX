import LeanFX2.HoTT.Path.Composition

/-! # HoTT/Path/Inverse — meta-level path inversion

Set-level path inversion built on Lean's `Eq.symm`.

## What ships

* `Path.symm  : Path A a b → Path A b a`
* `Path.symm_refl  : symm (refl x) = refl x`
* `Path.symm_symm  : symm (symm p) = p`
* `Path.symm_trans : symm (p . q) = symm q . symm p`
* `Path.trans_symm_left  : symm p . p = refl _`  (right inverse of trans)
* `Path.trans_symm_right : p . symm p = refl _`  (left  inverse of trans)

## Why these matter

The inverse laws + composition laws together give path the
**groupoid** structure used in `HoTT/Path/Groupoid.lean`.  At
set-level these laws are definitional (after `cases somePath`),
so no SN/confluence machinery is needed — Lean's pattern matcher
discharges everything.
-/

namespace LeanFX2

universe pathLevel

/-- Path inversion.  Wraps `Eq.symm`. -/
@[reducible] def Path.symm {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path rightEndpoint leftEndpoint :=
  Eq.symm somePath

/-- Inverting `refl` gives `refl`.  Definitional. -/
theorem Path.symm_refl {Carrier : Sort pathLevel}
    (someValue : Carrier) :
    Path.symm (Path.refl someValue) = Path.refl someValue := rfl

/-- Inversion is involutive.  Discharged by path induction. -/
theorem Path.symm_symm {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path.symm (Path.symm somePath) = somePath := by
  cases somePath
  rfl

/-- Inversion distributes over composition with order swap. -/
theorem Path.symm_trans {Carrier : Sort pathLevel}
    {endpoint0 endpoint1 endpoint2 : Carrier}
    (leftPath  : Path endpoint0 endpoint1)
    (rightPath : Path endpoint1 endpoint2) :
    Path.symm (Path.trans leftPath rightPath)
      = Path.trans (Path.symm rightPath) (Path.symm leftPath) := by
  cases leftPath
  cases rightPath
  rfl

/-- Left inverse of composition: `symm p . p = refl`. -/
theorem Path.trans_symm_left {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path.trans (Path.symm somePath) somePath
      = Path.refl rightEndpoint := by
  cases somePath
  rfl

/-- Right inverse of composition: `p . symm p = refl`. -/
theorem Path.trans_symm_right {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path.trans somePath (Path.symm somePath)
      = Path.refl leftEndpoint := by
  cases somePath
  rfl

/-! ## Smoke samples -/

example : Path.symm (Path.refl (3 : Nat)) = Path.refl 3 := rfl

end LeanFX2
