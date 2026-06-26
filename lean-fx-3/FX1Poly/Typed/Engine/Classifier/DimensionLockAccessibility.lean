import FX1Poly.Typed.Engine.Classifier.TypingContext

/-! # FX1Poly/Typed/DimensionLockAccessibility — the Fitch variable-accessibility discipline for the affine lock

The FitchTT TM/VAR variable-accessibility rule (MTT Fig 2, Gratzer-Kavvos-Nuyts-Birkedal 2021) specialized to
FX's single UNPOINTED AFFINE dimension lock (`TypingContext.lockCons`, mode-11/12, structure-class affine).

## The discipline (mode-axis-free for the affine fragment)

MTT's rule: a variable `x : (nu | A)` is usable at the ambient (fibrant) modality iff there is a 2-cell
`nu => locks(Gamma_after_x)`, where `locks(Gamma)` composes the lock modalities of the suffix after `x`
(`locks(empty) = 1`, `locks(cons) = locks(rest)`, `locks(lockCons) = locks(rest) . mu_affine`).

For FX's bridge the only lock is the affine dimension lock, at the UNPOINTED multiplier `mu_affine` (mode-12
unpointability): there is NO 2-cell `1 => mu_affine` and NO 2-cell `mu_affine => 1`.  So the general 2-cell
check collapses to a purely structural test on the telescope — NO `ModeGraph`/`ModalityPath` is needed yet (that
generalization is the later fib-3 wiring):

  * an ORDINARY variable (bound by `cons`, modality `1`) is fibrantly usable iff `1 => locks(suffix)` exists,
    i.e. iff `locks(suffix) = 1`, i.e. iff NO `lockCons` lies between its binding and the use point;
  * the DIMENSION variable (bound by `lockCons`, modality `mu_affine`) is NEVER fibrantly usable — fibrant use
    would need `mu_affine => 1`, which the unpointed multiplier does not provide.

`isFibrantlyAccessibleAt context index` decides exactly this: `true` iff the binding at `index` is a plain
`cons` AND no `lockCons` shadows it (lies strictly newer in the telescope).

## Why this is the subject-reduction fix (count-free, beta-stable)

The previous affine side condition was the syntactic occurrence count `gradedBinderChecks .one body`
(`occurrenceCountAt body 0 <= 1`), which is NOT beta-stable: `pathLam ((fn x : Interval => pair x x) i)` has
count 1 yet beta-reduces to `pathLam (pair i i)` with count 2, breaking subject reduction.  The Fitch discipline
replaces the count with a STRUCTURAL accessibility test on the CONTEXT: under `Gamma.lockCons Interval`, the
dimension `var 0` is not fibrantly accessible (`dimensionIsNotFibrantlyAccessible`), so `pair (var 0) (var 0)`
— a fibrant constructor applied to the locked dimension — does not type at all.  There is no count to break, so
`pathLam` subject reduction is structural.

This file ships the PREDICATE (the data of the discipline).  Wiring it into the variable typing rule (so every
bare fibrant variable use discharges it, a no-op `true` in any lock-free context) is the next increment.

## Zero-axiom verification

A `Bool`-valued structural recursion over the telescope with the `Fin` index destructured by the propext-free
`⟨0, _⟩` / `⟨position + 1, _⟩` structure match (the same recipe as `TypingContext.lookup`), plus `rfl`-closed
unfolders.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-- Decide whether the de Bruijn variable `index` may be used as a FIBRANT value in `context` under the Fitch
affine-lock discipline: `true` iff its binding is a plain `cons` and no `lockCons` shadows it (lies strictly
newer in the telescope).  The dimension bound by `lockCons` is never fibrantly accessible (the unpointed affine
multiplier has no 2-cell to the identity), and any binding behind a `lockCons` is likewise inaccessible.  The
mode-axis-free specialization of MTT's TM/VAR 2-cell check for the single affine lock. -/
def TypingContext.isFibrantlyAccessibleAt {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Fin scope → Bool
  | _, .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => true
  | _, .lockCons _ _, ⟨0, _⟩ => false
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons _ _, ⟨_position + 1, _⟩ => false

/-- Unfolder: the newest binding of a `cons` telescope is fibrantly accessible. -/
theorem isFibrantlyAccessibleAt_cons_zero {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.cons bindingType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = true :=
  rfl

/-- Unfolder: the newest binding of a `lockCons` telescope — the locked dimension — is NOT fibrantly accessible. -/
theorem isFibrantlyAccessibleAt_lockCons_zero {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = false :=
  rfl

/-- Unfolder: accessibility of a deeper variable past a `cons` binding recurses into the prefix (a plain `cons`
adds no lock to the suffix). -/
theorem isFibrantlyAccessibleAt_cons_succ {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (position : Nat) (isLtSuccSucc : position + 1 < scope + 1) :
    (restContext.cons bindingType).isFibrantlyAccessibleAt ⟨position + 1, isLtSuccSucc⟩ =
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩ :=
  rfl

/-- Unfolder: any variable that lies behind a `lockCons` (the lock is strictly newer than the variable) is NOT
fibrantly accessible — the lock shadows it. -/
theorem isFibrantlyAccessibleAt_lockCons_succ {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (position : Nat) (isLtSuccSucc : position + 1 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨position + 1, isLtSuccSucc⟩ = false :=
  rfl

/-- **★ The subject-reduction mechanism.**  The dimension bound by `lockCons` — `var 0` in the bridge body's
context — is NOT fibrantly accessible.  So a fibrant constructor applied to the dimension (the canonical
SR-breaker `pair (var 0) (var 0)`) cannot type once the variable rule discharges `isFibrantlyAccessibleAt`, and
the affine restriction is enforced STRUCTURALLY (by the context) rather than by a beta-fragile occurrence count.
This is the count-free, beta-stable replacement for `gradedBinderChecks .one`. -/
theorem dimensionIsNotFibrantlyAccessible {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = false :=
  rfl

end FX1Poly.Typed
