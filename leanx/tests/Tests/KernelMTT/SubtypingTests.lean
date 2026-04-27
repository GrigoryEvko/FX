import FX.KernelMTT.Term
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction
import FX.KernelMTT.Conversion
import FX.KernelMTT.Subtyping
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level
import FX.Kernel.Grade.Effect
import Tests.Framework

/-!
# FX.KernelMTT.Subtyping tests (V1.5 second installment)

Pinning tests for `Term.subtype` — T-sub on the well-scoped
mode-indexed Term, layered over `convEqWith` (V1.5-conv).

Twenty-two tests covering:

  * Reflexivity via convEq fast path (3)
  * U-cumul: Type<l1> <: Type<l2> when l1 ≤ l2 (5: true / true /
    false / refl / cross-mode)
  * Pi-subtype: contra-domain (2), co-codomain (2),
    effect-row subsumption (2), grade strict equality (1),
    mode mismatch (1)
  * Sigma-subtype: covariant fst (2), covariant snd (1)
  * forallLevel: covariant body (1)
  * β-reachable subtype via whnf (1)

These pin the operational behavior.  Soundness of `subtype`
against the kernel's conv judgement is V_meta scope.
-/

namespace Tests.KernelMTT.SubtypingTests

open Tests FX.KernelMTT FX.Kernel

/-! ## Builders -/

def natType {n : Nat} (m : Mode) : Term n := .ind m "Nat" .nil
def boolType {n : Nat} (m : Mode) : Term n := .ind m "Bool" .nil
def natZero {n : Nat} (m : Mode) : Term n :=
  .ctor m "Nat" 0 .nil .nil

def levelZero : Level := Level.zero
def levelOne  : Level := Level.succ Level.zero
def levelTwo  : Level := Level.succ (Level.succ Level.zero)

def run : IO Unit := Tests.suite "Tests.KernelMTT.SubtypingTests" do

  -----------------------------------------------------------
  -- Reflexivity via convEq fast path
  -----------------------------------------------------------

  -- 1. Same const reaches subtype via convEq fast path.
  check "reflexivity: const <: same const"
    true
    (Term.subtype (.const Mode.software "x" : Term 0)
                  (.const Mode.software "x"))

  -- 2. Same var index reaches subtype via convEq.
  check "reflexivity: var <: same var"
    true
    (Term.subtype (.var Mode.software 0 : Term 1)
                  (.var Mode.software 0))

  -- 3. Different consts: not in subtype relation.  No
  --    structural rule applies; convEq fails.
  check "different const: not subtype"
    false
    (Term.subtype (.const Mode.software "a" : Term 0)
                  (.const Mode.software "b"))

  -----------------------------------------------------------
  -- U-cumul: Type<l1> <: Type<l2> when l1 ≤ l2
  -----------------------------------------------------------

  -- 4. Type@0 <: Type@1.
  check "U-cumul: Type@0 <: Type@1"
    true
    (Term.subtype (.type Mode.software levelZero : Term 0)
                  (.type Mode.software levelOne))

  -- 5. Type@0 <: Type@2 (transitive cumulativity).
  check "U-cumul: Type@0 <: Type@2"
    true
    (Term.subtype (.type Mode.software levelZero : Term 0)
                  (.type Mode.software levelTwo))

  -- 6. Type@1 not <: Type@0 (cumulativity is one-directional).
  check "U-cumul: Type@1 not <: Type@0"
    false
    (Term.subtype (.type Mode.software levelOne : Term 0)
                  (.type Mode.software levelZero))

  -- 7. Type@0 <: Type@0 (reflexive — convEq fast path).
  check "U-cumul: Type@0 <: Type@0 (reflexive)"
    true
    (Term.subtype (.type Mode.software levelZero : Term 0)
                  (.type Mode.software levelZero))

  -- 8. Type@0 software vs Type@0 hardware: cross-mode not
  --    subtype (no cross-mode universe subtyping in v1).
  check "U-cumul: cross-mode rejected"
    false
    (Term.subtype (.type Mode.software levelZero : Term 0)
                  (.type Mode.hardware levelZero))

  -----------------------------------------------------------
  -- Pi: contra-domain, co-codomain, co-effect, strict grade
  -----------------------------------------------------------

  let piNatToBoolTot : Term 0 :=
    .pi Mode.software Grade.ghost (natType Mode.software)
        (boolType Mode.software) Effect.tot

  -- 9. Pi same shape: subtype via convEq fast path.
  check "Pi: same shape <: same shape (refl)"
    true
    (Term.subtype piNatToBoolTot piNatToBoolTot)

  -- 10. Pi contra-domain: (Type@1 → Bool) <: (Type@0 → Bool).
  --     Caller passes T : Type@0; callee at the supertype
  --     accepts any T : Type@1, which includes Type@0 by
  --     cumulativity.  Substitution direction admits.
  let piTypeOneToBool : Term 0 :=
    .pi Mode.software Grade.ghost (.type Mode.software levelOne)
        (boolType Mode.software) Effect.tot
  let piTypeZeroToBool : Term 0 :=
    .pi Mode.software Grade.ghost (.type Mode.software levelZero)
        (boolType Mode.software) Effect.tot
  check "Pi: (Type@1 → Bool) <: (Type@0 → Bool) [contra]"
    true
    (Term.subtype piTypeOneToBool piTypeZeroToBool)

  -- 11. Pi contra-domain reverse: (Type@0 → Bool) not <:
  --     (Type@1 → Bool).  Callee at the wider Type@1 cannot
  --     consume a fn that only accepts Type@0.
  check "Pi: (Type@0 → Bool) not <: (Type@1 → Bool)"
    false
    (Term.subtype piTypeZeroToBool piTypeOneToBool)

  -- 12. Pi co-codomain: (Bool → Type@0) <: (Bool → Type@1).
  --     Callee returns Type@0; caller accepts any Type@1
  --     return; cumulativity admits.
  let piBoolToTypeZero : Term 0 :=
    .pi Mode.software Grade.ghost (boolType Mode.software)
        (.type Mode.software levelZero) Effect.tot
  let piBoolToTypeOne : Term 0 :=
    .pi Mode.software Grade.ghost (boolType Mode.software)
        (.type Mode.software levelOne) Effect.tot
  check "Pi: (Bool → Type@0) <: (Bool → Type@1) [co]"
    true
    (Term.subtype piBoolToTypeZero piBoolToTypeOne)

  -- 13. Pi co-codomain reverse: (Bool → Type@1) not <:
  --     (Bool → Type@0).
  check "Pi: (Bool → Type@1) not <: (Bool → Type@0)"
    false
    (Term.subtype piBoolToTypeOne piBoolToTypeZero)

  -- 14. Pi effect subsumption: Tot <: IO at the row position.
  --     A function performing only Tot may be passed where
  --     an IO-row-permitting context is expected (it does
  --     less).
  let piNatToBoolIO : Term 0 :=
    .pi Mode.software Grade.ghost (natType Mode.software)
        (boolType Mode.software) Effect.io_
  check "Pi: (Nat → Bool with Tot) <: (... with IO) [eff subset]"
    true
    (Term.subtype piNatToBoolTot piNatToBoolIO)

  -- 15. Pi effect subsumption reverse: (with IO) not <:
  --     (with Tot).  An IO-performing fn cannot pass for a
  --     Tot context.
  check "Pi: (... with IO) not <: (... with Tot)"
    false
    (Term.subtype piNatToBoolIO piNatToBoolTot)

  -- 16. Pi grade strict equality on binders: ghost vs shared
  --     not subtype.  Grade subsumption on Pi binders is
  --     deferred (see Subtyping.lean docstring).
  let piShared : Term 0 :=
    .pi Mode.software Grade.shared (natType Mode.software)
        (boolType Mode.software) Effect.tot
  check "Pi: grade strict equality (ghost vs shared)"
    false
    (Term.subtype piNatToBoolTot piShared)

  -- 17. Pi mode mismatch: software vs hardware Pi not subtype.
  let piHardware : Term 0 :=
    .pi Mode.hardware Grade.ghost (natType Mode.hardware)
        (boolType Mode.hardware) Effect.tot
  check "Pi: mode mismatch software vs hardware"
    false
    (Term.subtype piNatToBoolTot piHardware)

  -----------------------------------------------------------
  -- Sigma: covariant in both positions
  -----------------------------------------------------------

  -- 18. Sigma covariant fst: (Type@0, Bool) <: (Type@1, Bool).
  let sigmaTypeZero : Term 0 :=
    .sigma Mode.software Grade.ghost
        (.type Mode.software levelZero)
        (boolType Mode.software)
  let sigmaTypeOne : Term 0 :=
    .sigma Mode.software Grade.ghost
        (.type Mode.software levelOne)
        (boolType Mode.software)
  check "Sigma: covariant fst (Type@0, Bool) <: (Type@1, Bool)"
    true
    (Term.subtype sigmaTypeZero sigmaTypeOne)

  -- 19. Sigma covariant fst reverse: (Type@1, Bool) not <:
  --     (Type@0, Bool).
  check "Sigma: covariant fst reverse direction"
    false
    (Term.subtype sigmaTypeOne sigmaTypeZero)

  -- 20. Sigma covariant snd: (Bool, Type@0) <: (Bool, Type@1).
  let sigmaBoolType0 : Term 0 :=
    .sigma Mode.software Grade.ghost
        (boolType Mode.software)
        (.type Mode.software levelZero)
  let sigmaBoolType1 : Term 0 :=
    .sigma Mode.software Grade.ghost
        (boolType Mode.software)
        (.type Mode.software levelOne)
  check "Sigma: covariant snd (Bool, Type@0) <: (Bool, Type@1)"
    true
    (Term.subtype sigmaBoolType0 sigmaBoolType1)

  -----------------------------------------------------------
  -- forallLevel: covariant body
  -----------------------------------------------------------

  -- 21. forallLevel covariant body: ∀L. Type@0 <: ∀L. Type@1.
  let faTypeZero : Term 0 :=
    .forallLevel Mode.software (.type Mode.software levelZero)
  let faTypeOne : Term 0 :=
    .forallLevel Mode.software (.type Mode.software levelOne)
  check "forallLevel: covariant body via cumulativity"
    true
    (Term.subtype faTypeZero faTypeOne)

  -----------------------------------------------------------
  -- β-reachable subtype via whnf
  -----------------------------------------------------------

  -- 22. β-reduction reaches a subtype-relevant whnf.
  --     `(λ x : Nat. Type@0) zero` reduces to `Type@0`, which
  --     is then a subtype of `Type@1` by U-cumul.  Verifies
  --     subtypeWith feeds whnf'd terms to subtypeWhnf.
  let lamConstType0 : Term 0 :=
    .lam Mode.software Grade.ghost (natType Mode.software)
        (.type Mode.software levelZero)
  let betaReachable : Term 0 :=
    .app Mode.software lamConstType0 (natZero Mode.software)
  check "β-reachable: (λx.Type@0) zero <: Type@1"
    true
    (Term.subtype betaReachable
                  (.type Mode.software levelOne))

end Tests.KernelMTT.SubtypingTests
