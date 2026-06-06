import FX1Poly.Typed.IsTypeDescDecidable
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion

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

/-- A telescope over `childCons` exposes its head typed at the SHARED flag.  Extracted via a single `cons`
case (the `nil` case is index-impossible, propext-clean exactly as in `decideAtFlag`'s refutations).  Used by
the flag-synthesizing decider to compare the synthesized head flag against an arbitrary telescope flag. -/
theorem DescTelescope.headTypedAtSharedFlag {profile : PolyProfile} {baseScope : Nat}
    {restShifts : List Nat} {context : TypingContext profile baseScope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {childHead : RawTerm (baseScope + 0)} {childTail : RawTermChildren restShifts baseScope}
    (telescope : DescTelescope profile (currentDepth := 0) context levels flag
      (.childCons childHead childTail)) :
    ∃ headLevel : LevelExpr,
      HasTypeDesc profile context childHead (universeCodeCell headLevel flag) := by
  cases telescope with
  | cons _armContext _armHead headLevel _restLevels _armFlag _armRest headTyped _restTyped =>
      exact ⟨headLevel, headTyped⟩

/-- **Flag-synthesizing telescope decider** — the bridge that lets the arity-generic `decideAtFlag` be called
WITHOUT knowing the shared universe flag in advance.  A former's children carry a stuck `generator.binderShifts`
index, so the former-type decider cannot pattern-match them; this helper takes a FREE `binderShifts` (matchable)
and SYNTHESISES the flag: `childNil` is a telescope at every flag (we report the canonical `.standard`);
`childCons` peeks the head (its binder shift must equal the telescope depth `0`, then its type fixes the shared
flag via `decideWithWitness`) and DELEGATES the whole-children telescope decision to `decideAtFlag` at that
synthesised flag.  Non-recursive — the spine recursion lives entirely in `decideAtFlag`.  The refutation is
flag-universal: no flag admits a telescope (the head's typing uniqueness collapses any candidate flag to the
synthesised one, where `decideAtFlag` already refuted). -/
def DescTelescope.decideWithSynthesizedFlag {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} (wellFormed : WfContextDesc context) :
    {binderShifts : List Nat} → (children : RawTermChildren binderShifts baseScope) →
    PSum
      (Σ' flag : UniverseFlag, Σ' levels : List LevelExpr,
        DescTelescope profile (currentDepth := 0) context levels flag children)
      ((flag : UniverseFlag) → (levels : List LevelExpr) →
        DescTelescope profile (currentDepth := 0) context levels flag children → False)
  | _, .childNil =>
      .inl ⟨UniverseFlag.standard, [],
        DescTelescope.nil (baseScope := baseScope) (currentDepth := 0) context UniverseFlag.standard⟩
  | _, @RawTermChildren.childCons _ shift _ childHead childTail =>
      if hShift : shift = 0 then by
        subst hShift
        exact (match IsTypeDesc.decideWithWitness wellFormed childHead with
          | .inr headNotType =>
              .inr (fun flag _levels telescope => by
                cases telescope with
                | cons _ctx _hd headLevel _rl _fl _rst headTyped _rt =>
                    exact headNotType ⟨headLevel, flag, headTyped⟩)
          | .inl ⟨headLevel, headFlag, headTyped⟩ =>
              match DescTelescope.decideAtFlag headFlag (currentDepth := 0) context wellFormed
                  (.childCons childHead childTail) with
              | .inl ⟨levels, telescope⟩ =>
                  .inl ⟨headFlag, levels, telescope⟩
              | .inr noTelescopeAtHeadFlag =>
                  .inr (fun _flag levels telescope => by
                    obtain ⟨_telHeadLevel, telHeadTyped⟩ := telescope.headTypedAtSharedFlag
                    obtain ⟨_, flagAgree⟩ :=
                      universeCodeCell_inj_of_conv
                        (HasTypeDesc.uniquenessNative telHeadTyped wellFormed headTyped)
                    subst flagAgree
                    exact noTelescopeAtHeadFlag levels telescope))
      else by
        exact .inr (fun _flag _levels telescope => by
          cases telescope with
          | cons _ctx _hd _headLevel _restLevels _flg _rst _headTyped _restTyped =>
              exact hShift rfl)

/-- **Arity-generic former-type decider (GTL-10 heart).**  Decides whether a formation former
`mkGen generator payload children` (with `typingRuleDescOf generator = some rule`) inhabits some universe — the
cascade-free replacement for the hand-written Π / Σ branches plus the `typingRuleDescOf_isPiOrSigma` refutation
`else` in `IsTypeDesc.decideWithWitness`.  Names NO formation generator: it asks `decideWithSynthesizedFlag`
whether the children form a telescope at some shared flag, then either reassembles the former via the generic
`HasTypeDesc.genFormation` arm (rewriting the rule output to the universe code via
`typingRuleDescOf_outputIsUniverseFormer`) or refutes — any putative typing inverts (generically, via
`inversionFormerWithConvGeneric`) to a telescope at SOME flag, which the flag-universal refutation rejects.  A
new formation row (`listCode`/`optionCode`/…) is absorbed with zero new arms. -/
def IsTypeDesc.decideFormerType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    PSum
      (Σ' levelExpr : LevelExpr, Σ' flag : UniverseFlag,
        HasTypeDesc profile context (.mkGen generator payload children)
          (universeCodeCell levelExpr flag))
      (IsTypeDesc profile context (.mkGen generator payload children) → False) :=
  match DescTelescope.decideWithSynthesizedFlag wellFormed children with
  | .inl ⟨flag, levels, telescope⟩ =>
      .inl ⟨lmaxAll levels, flag, by
        have formerTyped :=
          HasTypeDesc.genFormation context generator payload children levels flag rule isFormation telescope
        rw [typingRuleDescOf_outputIsUniverseFormer isFormation] at formerTyped
        exact formerTyped⟩
  | .inr noTelescopeAtAnyFlag =>
      .inr (fun isType => by
        obtain ⟨_levelExpr, _flag, typed⟩ := isType
        obtain ⟨levels, telFlag, telescope, _convToCode⟩ :=
          HasTypeDesc.inversionFormerWithConvGeneric typed isFormation rfl
        exact noTelescopeAtAnyFlag telFlag levels telescope)

/-- **Cascade-free non-leaf `IsTypeDesc` decision (the GTL-10 former dispatch).**  Decides whether a
`mkGen generator payload children` whose root is NEITHER `gen_var` NOR `gen_universeCode` inhabits some
universe — the exact cascade-free replacement for `IsTypeDesc.decideWithWitness`'s hand-written Π / Σ branches
PLUS its `typingRuleDescOf_isPiOrSigma` `else` refutation.  It dispatches the formation table directly:
`typingRuleDescOf generator = some rule` routes to the arity-generic `decideFormerType`; `= none` refutes
table-generically via `not_of_rootGenerator` (a non-var non-universe non-formation root is never a formation
type).  Names NO formation generator — a future formation row (`listCode`/…) is absorbed into the `some`
branch with zero new arms, the FRAME-2 extensibility property.  The two leaf exclusions arrive as hypotheses:
this is the NON-LEAF half of the eventual cascade-free `decideWithWitness`, factored out so it depends only on
already-defined deciders (no mutual recursion — the leaf `var`/`universeCode` recursion stays in
`decideWithWitness`). -/
def IsTypeDesc.decideMkGenOfNonLeaf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    {generator : Generator}
    (notVariable : generator ≠ Generator.gen_var)
    (notUniverseCode : generator ≠ Generator.gen_universeCode)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    PSum
      (Σ' levelExpr : LevelExpr, Σ' flag : UniverseFlag,
        HasTypeDesc profile context (.mkGen generator payload children)
          (universeCodeCell levelExpr flag))
      (IsTypeDesc profile context (.mkGen generator payload children) → False) :=
  match hGen : typingRuleDescOf generator with
  | some _rule => IsTypeDesc.decideFormerType wellFormed hGen payload children
  | none => .inr (IsTypeDesc.not_of_rootGenerator notVariable notUniverseCode hGen)

end FX1Poly.Typed
