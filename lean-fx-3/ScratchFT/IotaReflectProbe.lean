import FX1Poly.Core.StepRenameReflect

/-! Probe: the boolElim/boolTrue ι child-projection reflection arm. NEVER committed. -/

namespace FX1Poly.Core.Spike
open FX1Poly.Foundation

theorem reflectIotaBoolTrue {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedThen renamedElse : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_boolElim ()
        (.childCons (.mkGen .gen_boolTrue () .childNil)
          (.childCons renamedThen (.childCons renamedElse .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedThen := by
  -- recover the boolElim head
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  -- children : RawTermChildren gen_boolElim.binderShifts sourceScope; decompose
  match payload, children with
  | (), .childCons scrut (.childCons thenB (.childCons elseB .childNil)) =>
      -- distribute rename over the concrete boolElim cell (try rfl)
      rw [show RawTerm.rename rho
            (.mkGen .gen_boolElim ()
              (.childCons scrut (.childCons thenB (.childCons elseB .childNil)))) =
            (.mkGen .gen_boolElim ()
              (.childCons (RawTerm.rename rho scrut)
                (.childCons (RawTerm.rename rho thenB)
                  (.childCons (RawTerm.rename rho elseB) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _genEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutEq tailEq
      injection tailEq with _ _ _ thenEq tail2Eq
      injection tail2Eq with _ _ _ elseEq _
      -- scrutEq : rename rho scrut = mkGen gen_boolTrue () childNil ; recover scrut = boolTrue
      obtain ⟨scrutPayload, scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutEq
      subst scrutTermEq
      match scrutPayload, scrutChildren with
      | (), .childNil =>
          refine ⟨thenB, Step.iotaBoolTrue, ?_⟩
          exact thenEq

end FX1Poly.Core.Spike
