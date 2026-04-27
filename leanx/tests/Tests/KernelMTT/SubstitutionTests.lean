import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level
import Tests.Framework

/-!
# FX.KernelMTT.Substitution tests (W3)

Pinning tests for `Term.shift`, `Term.shift0`, `Term.substAt`,
`Term.subst` against the well-scoped `Term : Nat → Type` of W2.

Eighteen tests covering:

  * `shift` basics — variables below / above the cut, identity
    on closed terms, mode preservation (4 tests)
  * `shift` through binders — bound vars stay; free vars lift
    (2 tests)
  * `subst` basics — three index cases (i < k, i = k, i > k) at
    multiple positions (5 tests)
  * β-reduction shape — `(λx. x) arg ↦ arg` (1 test)
  * Round-trip — `subst (shift t) anything = t` for closed and
    open terms (2 tests)
  * Multi-arg structures — shift through `ind` / TermArgs
    (1 test)
  * Cross-mode primitives — modIntro, modElim shifting,
    body-context extension correctness (2 tests)
  * Subst through binder — body's free outer var becomes
    shifted-arg, modulo the +1 cut and shift0 dance (1 test)
-/

namespace Tests.KernelMTT.SubstitutionTests

open Tests FX.KernelMTT FX.Kernel

/-! ## Builders -/

def natType  {n : Nat} (m : Mode) : Term n := .ind m "Nat" .nil
def natZero  {n : Nat} (m : Mode) : Term n := .ctor m "Nat" 0 .nil .nil

def run : IO Unit := Tests.suite "Tests.KernelMTT.SubstitutionTests" do

  -----------------------------------------------------------
  -- shift basics
  -----------------------------------------------------------

  -- 1. shift cut on var below cut: index unchanged.
  let v0 : Term 2 := Term.var Mode.software 0
  let s0 : Term 3 := Term.shift 1 v0
  check "shift 1 at var 0 stays var 0"
    true
    (Term.structEq s0 (Term.var Mode.software 0))

  -- 2. shift cut on var ≥ cut: index +1.
  let v1 : Term 2 := Term.var Mode.software 1
  let s1 : Term 3 := Term.shift 1 v1
  check "shift 1 at var 1 becomes var 2"
    true
    (Term.structEq s1 (Term.var Mode.software 2))

  -- 3. shift0 on any var k always shifts to var (k+1).
  let v_zero : Term 1 := Term.var Mode.software 0
  let shifted : Term 2 := Term.shift0 v_zero
  check "shift0 at var 0 becomes var 1"
    true
    (Term.structEq shifted (Term.var Mode.software 1))

  -- 4. shift preserves the term's mode (Term.mode projection).
  let v_ghost : Term 1 := Term.var Mode.ghost 0
  let s_ghost : Term 2 := Term.shift0 v_ghost
  check "shift0 preserves Ghost mode"
    Mode.ghost
    s_ghost.mode

  -----------------------------------------------------------
  -- shift through binders
  -----------------------------------------------------------

  -- 5. shift0 through a lambda: the body's bound var 0 is
  --    shifted at cut=1 (because we're now under the binder)
  --    so it stays at index 0.
  let lam0 : Term 0 :=
    Term.lam Mode.software Grade.ghost
      (natType Mode.software) (Term.var Mode.software 0)
  let shifted_lam : Term 1 := Term.shift0 lam0
  let expected_shifted : Term 1 :=
    Term.lam Mode.software Grade.ghost
      (natType Mode.software) (Term.var Mode.software 0)
  check "shift0 through lam: bound var 0 stays var 0"
    true
    (Term.structEq shifted_lam expected_shifted)

  -- 6. shift0 through a lambda with a free var: the body's
  --    var 1 (which references the outer scope, not the bound
  --    var) shifts to var 2.
  let lam_free : Term 1 :=
    Term.lam Mode.software Grade.ghost
      (natType Mode.software) (Term.var Mode.software 1)
  let shifted_lam_free : Term 2 := Term.shift0 lam_free
  let expected_lf : Term 2 :=
    Term.lam Mode.software Grade.ghost
      (natType Mode.software) (Term.var Mode.software 2)
  check "shift0 through lam: free var 1 shifts to var 2"
    true
    (Term.structEq shifted_lam_free expected_lf)

  -----------------------------------------------------------
  -- subst basics — three index cases at multiple positions
  -----------------------------------------------------------

  -- 7. β-substitution at 0 with body=var 0: result equals arg.
  let body_v0 : Term 1 := Term.var Mode.software 0
  let arg : Term 0 := natZero Mode.software
  let r7 : Term 0 := Term.subst body_v0 arg
  check "subst at 0: body=var 0 yields arg"
    true
    (Term.structEq r7 arg)

  -- 8. substAt 0 with body=var 1: var 1 decrements to var 0.
  let body_v1 : Term 2 := Term.var Mode.software 1
  let arg1 : Term 1 := natZero Mode.software
  let r8 : Term 1 := Term.substAt ⟨0, by omega⟩ arg1 body_v1
  check "subst at 0: body=var 1 decrements to var 0"
    true
    (Term.structEq r8 (Term.var Mode.software 0))

  -- 9. substAt 1 with body=var 0: index < k stays unchanged.
  let body_v0_in_2 : Term 2 := Term.var Mode.software 0
  let arg2 : Term 1 := natZero Mode.software
  let r9 : Term 1 :=
    Term.substAt ⟨1, by omega⟩ arg2 body_v0_in_2
  check "subst at 1: body=var 0 stays var 0"
    true
    (Term.structEq r9 (Term.var Mode.software 0))

  -- 10. substAt 1 with body=var 1: index = k yields arg.
  let body_v1_in_2 : Term 2 := Term.var Mode.software 1
  let r10 : Term 1 :=
    Term.substAt ⟨1, by omega⟩ arg2 body_v1_in_2
  check "subst at 1: body=var 1 yields arg"
    true
    (Term.structEq r10 arg2)

  -- 11. substAt 1 with body=var 2: index > k decrements.
  let body_v2_in_3 : Term 3 := Term.var Mode.software 2
  let arg3 : Term 2 := natZero Mode.software
  let r11 : Term 2 :=
    Term.substAt ⟨1, by omega⟩ arg3 body_v2_in_3
  check "subst at 1: body=var 2 decrements to var 1"
    true
    (Term.structEq r11 (Term.var Mode.software 1))

  -----------------------------------------------------------
  -- β-reduction shape
  -----------------------------------------------------------

  -- 12. β-reduction: (λ x : Nat. x) arg ↦ arg.  Pin the shape
  --     of the substitution result against the bare arg.
  let id_body : Term 1 := Term.var Mode.software 0
  let beta_arg : Term 0 := natZero Mode.software
  let beta_result : Term 0 := Term.subst id_body beta_arg
  check "β: identity-lam applied to arg yields arg"
    true
    (Term.structEq beta_result beta_arg)

  -----------------------------------------------------------
  -- Round-trip identity
  -----------------------------------------------------------

  -- 13. shift then subst at 0 with anything = identity, on a
  --     closed term.  shift0 inserts a fresh var 0 nobody
  --     references; subst at 0 removes it; result equals
  --     input.
  let closed : Term 0 := natZero Mode.software
  let any_arg : Term 0 := natZero Mode.ghost
  let rt1 : Term 0 := Term.subst (Term.shift0 closed) any_arg
  check "shift0 then subst at 0: identity (closed)"
    true
    (Term.structEq rt1 closed)

  -- 14. Same identity on a term with a free var.
  let with_var : Term 1 := Term.var Mode.software 0
  let any_arg_open : Term 1 := natZero Mode.ghost
  let rt2 : Term 1 := Term.subst (Term.shift0 with_var) any_arg_open
  check "shift0 then subst at 0: identity (open, var 0)"
    true
    (Term.structEq rt2 with_var)

  -----------------------------------------------------------
  -- shift through TermArgs
  -----------------------------------------------------------

  -- 15. shift recurses through `ind` arg lists.  An ind type
  --     applied to a free-var argument shifts that argument.
  let ind_t : Term 1 :=
    Term.ind Mode.software "Box"
      (TermArgs.ofList [Term.var Mode.software 0])
  let shifted_ind : Term 2 := Term.shift0 ind_t
  let expected_ind : Term 2 :=
    Term.ind Mode.software "Box"
      (TermArgs.ofList [Term.var Mode.software 1])
  check "shift0 recurses through ind args"
    true
    (Term.structEq shifted_ind expected_ind)

  -----------------------------------------------------------
  -- shift on cross-mode constructors
  -----------------------------------------------------------

  -- 16. shift0 through modIntro: target mode preserved
  --     (Term.mode projects target for cross-mode forms).
  let mi : Term 1 :=
    Term.modIntro Mode.ghost Mode.software
      Modality.usage (Term.var Mode.ghost 0)
  let shifted_mi : Term 2 := Term.shift0 mi
  check "shift0 through modIntro: target mode preserved"
    Mode.software
    shifted_mi.mode

  -- 17. shift0 through modElim: body extends ctx, so its
  --     bound var 0 stays at 0 (cut becomes 1 inside body).
  let me0 : Term 1 :=
    Term.modElim Mode.software Mode.ghost Modality.usage
      (Term.const Mode.software "x")
      (Term.var Mode.ghost 0)
  let shifted_me : Term 2 := Term.shift0 me0
  let expected_me : Term 2 :=
    Term.modElim Mode.software Mode.ghost Modality.usage
      (Term.const Mode.software "x")
      (Term.var Mode.ghost 0)
  check "shift0 through modElim: body's bound var 0 stays"
    true
    (Term.structEq shifted_me expected_me)

  -----------------------------------------------------------
  -- subst through binder: body free outer var becomes shifted-arg
  -----------------------------------------------------------

  -- 18. subst into a lambda: the body's reference to the
  --     outer free var (var 1 inside the body, since var 0 is
  --     the lam's binder) becomes the shifted arg.
  let outer_lam : Term 1 :=
    Term.lam Mode.software Grade.ghost (natType Mode.software)
      (Term.var Mode.software 1)
  let arg18 : Term 0 := natZero Mode.software
  let r18 : Term 0 := Term.subst outer_lam arg18
  let expected18 : Term 0 :=
    Term.lam Mode.software Grade.ghost (natType Mode.software)
      (Term.shift0 (natZero Mode.software))
  check "subst into lam: body's outer var becomes shifted arg"
    true
    (Term.structEq r18 expected18)

end Tests.KernelMTT.SubstitutionTests
