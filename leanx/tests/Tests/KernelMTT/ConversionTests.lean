import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction
import FX.KernelMTT.Conversion
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level
import Tests.Framework

/-!
# FX.KernelMTT.Conversion tests (V1.5 first installment)

Pinning tests for `Term.convEq` — definitional equality modulo
the V1.15 reduction rules plus η on Lam.

Twenty tests covering:

  * Reflexivity on closed terms (1)
  * Different vars / different consts → false (2)
  * β-reduction equates `(λ x. x) zero` and `zero` (1)
  * η on Lam (one direction): `λ x. f x ≡ f` (1)
  * η on Lam (other direction): `f ≡ λ x. f x` (1)
  * η-precondition: identity λ ≠ unrelated const (1)
  * Mode mismatch on same-shape lam → false (1)
  * Grade mismatch on same-shape lam → false (1)
  * Type-name mismatch on ind → false (1)
  * Reductions reachable through whnf — ι, ν, modElim-ι,
    idJ-ι, coerceCell-strip (5)
  * Pi convertibility — same vs different effect (2)
  * Type / forallLevel / nested-app reflexivity (3)

These pin the operational behaviour.  Mechanized
soundness/completeness theorems are V_meta scope.
-/

namespace Tests.KernelMTT.ConversionTests

open Tests FX.KernelMTT FX.Kernel

/-! ## Builders -/

def natType {n : Nat} (m : Mode) : Term n := .ind m "Nat" .nil
def natZero {n : Nat} (m : Mode) : Term n := .ctor m "Nat" 0 .nil .nil
def boolTrue  {n : Nat} (m : Mode) : Term n := .ctor m "Bool" 1 .nil .nil

/-- Identity lambda `λ x : Nat. x` at the given mode, closed. -/
def idLam (m : Mode) : Term 0 :=
  .lam m Grade.ghost (natType m) (.var m 0)

def run : IO Unit := Tests.suite "Tests.KernelMTT.ConversionTests" do

  -----------------------------------------------------------
  -- Reflexivity / negative basics
  -----------------------------------------------------------

  -- 1. Reflexivity: convEq of a complex term with itself.
  let complexTerm : Term 0 :=
    .app Mode.software (idLam Mode.software)
      (natZero Mode.software)
  check "reflexivity on complex term"
    true
    (Term.convEq complexTerm complexTerm)

  -- 2. Different de Bruijn vars: false.
  check "convEq rejects different var indices"
    false
    (Term.convEq (.var Mode.software 0 : Term 2)
                 (.var Mode.software 1))

  -- 3. Different const names: false.
  check "convEq rejects different const names"
    false
    (Term.convEq (.const Mode.software "a" : Term 0)
                 (.const Mode.software "b"))

  -----------------------------------------------------------
  -- β-equality (via whnf in convEq)
  -----------------------------------------------------------

  -- 4. β: `(λ x. x) zero ≡ zero`.  whnf reduces the lhs to
  --     `zero`; rhs is already `zero`; convEq accepts.
  let lhs4 : Term 0 :=
    .app Mode.software (idLam Mode.software)
      (natZero Mode.software)
  let rhs4 : Term 0 := natZero Mode.software
  check "β: (λx. x) zero ≡ zero"
    true
    (Term.convEq lhs4 rhs4)

  -----------------------------------------------------------
  -- η on Lam — both directions and the negative case
  -----------------------------------------------------------

  -- 5. η (lhs is lam): `λ x : Nat. f x ≡ f` where `f` has no
  --    free var binding to `x`.  shift0 lifts `f` over the
  --    new binder; the body is `app m (shift0 f) (var 0)`,
  --    which is exactly the η-expansion.
  let f5 : Term 0 := .const Mode.software "f"
  let lhs5 : Term 0 :=
    .lam Mode.software Grade.ghost (natType Mode.software)
      (.app Mode.software (Term.shift0 f5)
        (.var Mode.software 0))
  check "η: λx. f x ≡ f"
    true
    (Term.convEq lhs5 f5)

  -- 6. η (rhs is lam): symmetric direction.
  check "η: f ≡ λx. f x"
    true
    (Term.convEq f5 lhs5)

  -- 7. η-precondition fails: identity λ vs unrelated const.
  --    The λ body references `var 0` but η-expansion of
  --    `const "f"` produces `app f (var 0)` — different
  --    structure.
  check "η: id ≠ const (different bodies)"
    false
    (Term.convEq (idLam Mode.software) f5)

  -----------------------------------------------------------
  -- Constructor / mode / grade mismatches
  -----------------------------------------------------------

  -- 8. Mode mismatch on same-shape lam.
  check "mode mismatch on lam"
    false
    (Term.convEq (idLam Mode.software) (idLam Mode.hardware))

  -- 9. Grade mismatch on same-shape lam.
  let ghostLam : Term 0 :=
    .lam Mode.software Grade.ghost (natType Mode.software)
      (.var Mode.software 0)
  let sharedLam : Term 0 :=
    .lam Mode.software Grade.shared (natType Mode.software)
      (.var Mode.software 0)
  check "grade mismatch on lam"
    false
    (Term.convEq ghostLam sharedLam)

  -- 10. Type-name mismatch on ind: Bool vs Nat with same args.
  check "type-name mismatch on ind"
    false
    (Term.convEq (.ind Mode.software "Bool" .nil : Term 0)
                 (.ind Mode.software "Nat" .nil))

  -----------------------------------------------------------
  -- Reductions reachable through whnf
  -----------------------------------------------------------

  -- 11. ι: indRec on Bool true reaches the true method.
  let methF : Term 0 := .const Mode.software "false_method"
  let methT : Term 0 := .const Mode.software "true_method"
  let mot   : Term 0 := .const Mode.software "motive"
  let iotaLhs : Term 0 :=
    .indRec Mode.software "Bool" mot
      (TermArgs.ofList [methF, methT])
      (boolTrue Mode.software)
  check "ι via whnf: indRec Bool true ≡ true method"
    true
    (Term.convEq iotaLhs methT)

  -- 12. ν: coindDestruct(tail) on coindUnfold reaches tail arm.
  let headArm : Term 0 := .const Mode.software "head_body"
  let tailArm : Term 0 := .const Mode.software "tail_body"
  let unfold : Term 0 :=
    .coindUnfold Mode.software "Stream"
      (TermArgs.ofList [natType Mode.software])
      (TermArgs.ofList [headArm, tailArm])
  let nuLhs : Term 0 :=
    .coindDestruct Mode.software "Stream" 1 unfold
  check "ν via whnf: coindDestruct(tail) ≡ tail arm"
    true
    (Term.convEq nuLhs tailArm)

  -- 13. modElim-ι: modElim on matching modIntro reaches
  --     subst-body-by-inner result.
  let mInner : Term 0 := natZero Mode.ghost
  let modIntroT : Term 0 :=
    .modIntro Mode.ghost Mode.software Modality.usage mInner
  let elimBody : Term 1 := .var Mode.ghost 0
  let modElimLhs : Term 0 :=
    .modElim Mode.software Mode.ghost Modality.usage
      modIntroT elimBody
  check "modElim-ι via whnf: matched modality ≡ subst body inner"
    true
    (Term.convEq modElimLhs mInner)

  -- 14. idJ-ι: idJ mot base (refl w) ≡ app m base w.
  let baseFn : Term 0 := .const Mode.software "j_base"
  let witness : Term 0 := natZero Mode.software
  let idJLhs : Term 0 :=
    .idJ Mode.software mot baseFn
      (.refl Mode.software witness)
  let idJRhs : Term 0 :=
    .app Mode.software baseFn witness
  check "idJ-ι via whnf: idJ mot base (refl w) ≡ app m base w"
    true
    (Term.convEq idJLhs idJRhs)

  -- 15. coerceCell strip: convEq sees through the coercion.
  let wrapped : Term 0 :=
    .coerceCell Modality.usage "from" "to"
      (natZero Mode.software)
  check "coerceCell-strip via whnf: wrapped ≡ inner"
    true
    (Term.convEq wrapped (natZero Mode.software))

  -----------------------------------------------------------
  -- Pi convertibility (effect / domain / body)
  -----------------------------------------------------------

  -- 16. Same Pi: convertible.
  let piA : Term 0 :=
    .pi Mode.software Grade.ghost (natType Mode.software)
        (natType Mode.software) Effect.tot
  check "Pi-Pi same shape, same effect: convertible"
    true
    (Term.convEq piA piA)

  -- 17. Pi-Pi different return effect: not convertible.
  let piIO : Term 0 :=
    .pi Mode.software Grade.ghost (natType Mode.software)
        (natType Mode.software) Effect.io_
  check "Pi-Pi different return effect: not convertible"
    false
    (Term.convEq piA piIO)

  -----------------------------------------------------------
  -- Reflexivity on type-level / quantifier / nested-app forms
  -----------------------------------------------------------

  -- 18. Type at level 0 vs same: convertible.
  check "Type@Software level 0 reflexive"
    true
    (Term.convEq (.type Mode.software Level.zero : Term 0)
                 (.type Mode.software Level.zero))

  -- 19. forallLevel reflexive (level binder doesn't extend
  --     term ctx, but body convertibility still recurses).
  let fa : Term 1 :=
    .forallLevel Mode.software (.var Mode.software 0)
  check "forallLevel reflexive"
    true
    (Term.convEq fa fa)

  -- 20. Nested β + structural: `((λx. x) zero) ≡ zero` even
  --     when wrapped in another app — exercises whnf
  --     recursing into nested heads.
  let nested : Term 0 :=
    .app Mode.software
      (.app Mode.software (idLam Mode.software)
        (idLam Mode.software))
      (natZero Mode.software)
  check "nested β reaches zero"
    true
    (Term.convEq nested (natZero Mode.software))

end Tests.KernelMTT.ConversionTests
