import FX1Poly.Typed.IsTypeDescDecidable
import FX1Poly.Typed.DescTelescopeInversion

/-! # FX1Poly/Typed/DescTelescopeDecidable
    — the ARITY-GENERIC recursive telescope-typing decider (GTL-10 substrate, the extensibility gate)

The native `IsTypeDesc` decider (`IsTypeDescDecidable.lean`) handles the formation formers Π / Σ by two
HAND-WRITTEN two-child branches plus a refutation `else` branch that enumerates the formation table
(`typingRuleDescOf_isPiOrSigma`).  That enumeration is the cascade trap (polycell.md §3.16.19, FRAME-2): the
moment a new formation row lands — a data type code (`listCode`/`optionCode`/…), a cubical former, a HIT — the
decider must gain a branch.

This file ships the cascade-free core: a single RECURSIVE decision procedure over the children spine that
decides whether the children of ANY former form a valid `DescTelescope` premise (each child a type at a
SHARED universe flag, the codomain-style children checked under the binder-extended context), with NO
generator named.  Structural recursion on `children` — so the per-child binder shift peels off naturally and
the dependent `binderShifts` index never needs a transport (the documented GTL-08 "arity-bound wall" is
dodged by recursing on the spine rather than casting the shift list).

> `DescTelescope.decideAtFlag flag context wellFormed children` returns either a witness
> `Σ' levels, DescTelescope context levels flag children` (the children ARE a telescope at `flag`) or a proof
> that no `levels` makes them one.

The shared flag is threaded as the parameter `flag`; the level list is SYNTHESISED (each child contributes
its own universe level via the native `IsTypeDesc.decideWithWitness`).  A `childCons` whose binder shift does
not equal the current telescope depth, a non-type child, or a child at the wrong flag each refute — by casing
the (would-be) telescope back to its `cons` constructor and contradicting via index mismatch / native
typing-uniqueness.

## Zero-axiom verification

Structural recursion on `children`; the leaves are the shipped `IsTypeDesc.decideWithWitness` (native, off the
old engine) + `WfContextDesc.cons` + `DescTelescope.nil/.cons`; the refutations case the telescope (single live
`cons` arm, `childNil`/depth-mismatch refuted by the spine index) and use `HasTypeDesc.uniquenessNative` +
`universeCodeCell_inj_of_conv` for the flag clash.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Arity-generic telescope-typing decider (GTL-10 core).**  Decides whether `children` form a
`DescTelescope` premise at the shared universe `flag` and current depth, synthesising the per-child level
list.  Recurses structurally on the children spine: `childNil` is the empty telescope; `childCons` decides the
head is a type at `flag` (after confirming its binder shift matches the current depth) and recurses on the tail
under the binder-extended context.  The refutation arms case the would-be telescope to its `cons` constructor
and contradict the failing condition.  No formation generator is named — a new formation row is absorbed
zero-touch. -/
def DescTelescope.decideAtFlag {profile : PolyProfile} {baseScope : Nat}
    (flag : UniverseFlag) :
    {currentDepth : Nat} → {binderShifts : List Nat} →
    (context : TypingContext profile (baseScope + currentDepth)) →
    WfContextDesc context →
    (children : RawTermChildren binderShifts baseScope) →
    PSum
      (Σ' levels : List LevelExpr,
        DescTelescope profile (currentDepth := currentDepth) context levels flag children)
      ((levels : List LevelExpr) →
        DescTelescope profile (currentDepth := currentDepth) context levels flag children → False)
  | _currentDepth, _, context, _wellFormed, .childNil =>
      .inl ⟨[], DescTelescope.nil context flag⟩
  | currentDepth, _, context, wellFormed,
      @RawTermChildren.childCons _ shift _ childHead childTail =>
      if hShift : shift = currentDepth then by
        subst hShift
        exact (match IsTypeDesc.decideWithWitness wellFormed childHead with
          | .inr headNotType =>
              .inr (fun _levels telescope => by
                cases telescope with
                | cons _ctx _hd headLevel _restLevels _flg _rst headTyped _restTyped =>
                    exact headNotType ⟨headLevel, flag, headTyped⟩)
          | .inl ⟨headLevel, headFlag, headTyped⟩ =>
              if hFlag : headFlag = flag then by
                subst headFlag
                exact (match DescTelescope.decideAtFlag flag
                    (currentDepth := shift + 1) (context.cons childHead)
                    (WfContextDesc.cons wellFormed ⟨headLevel, flag, headTyped⟩) childTail with
                  | .inl ⟨restLevels, restTelescope⟩ =>
                      .inl ⟨headLevel :: restLevels,
                        DescTelescope.cons context childHead headLevel restLevels flag childTail
                          headTyped restTelescope⟩
                  | .inr restRefutes =>
                      .inr (fun _levels telescope => by
                        cases telescope with
                        | cons _ctx _hd _headLevel restLevels _flg _rst _headTyped restTyped =>
                            exact restRefutes restLevels restTyped))
              else
                .inr (fun _levels telescope => by
                  cases telescope with
                  | cons _ctx _hd telHeadLevel _restLevels _flg _rst telHeadTyped _restTyped =>
                      obtain ⟨_, flagAgree⟩ :=
                        universeCodeCell_inj_of_conv
                          (HasTypeDesc.uniquenessNative headTyped wellFormed telHeadTyped)
                      exact hFlag flagAgree))
      else
        .inr (fun _levels telescope => by
          cases telescope with
          | cons _ctx _hd _headLevel _restLevels _flg _rst _headTyped _restTyped =>
              exact hShift rfl)

end FX1Poly.Typed
