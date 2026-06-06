import FX1Poly.Typed.HasTypeDescElim
import FX1Poly.Typed.HasTypeDescElimWeakening
import FX1Poly.Typed.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeDescElimSubstitution — INTRINSIC substitution (P6, the β-engine)
    for the ELIMINATOR-shape term spine `DescTermTelescope`.

polycell.md §11.8.5 P6 ("Substitution / weakening = whiskering, the β-engine"): typing is
preserved along a context morphism.  This file carries the SUBSTITUTION half for
`DescTermTelescope` (HasTypeDescElim) — the maximally-general typed-children spine the
eliminator `gen`-arm consumes — paired with the renaming/weakening half
(`HasTypeDescElimWeakening`).  Together they are the eliminator spine's two fibration legs
(cartesian lift + β-substitution).

## Self-recursion over the HasTypeDesc β-engine (NON-breaking)

`DescTermTelescope` is a STANDALONE inductive (`HasTypeDesc` appears only positively in
`cons`'s `headTyped`), so this touches neither `HasTypeDesc`'s constructors nor the
`toHasType` ⟺ soundness map.  The head child's typing is re-substituted by cross-calling
`HasTypeDesc.substRespectingContext` on the opaque `headTyped`; the only recursion is on the
strictly-smaller `restTyped`, so Lean's structural recursion lands it without
`termination_by` — the same self-recursive shape as
`DescTermTelescope.renameRespectingTermTelescope` and `DescTelescope.toTermTelescope`.

## The arbitrary classifier substitutes generically; the decouple compounds

Because the conclusion index omits the per-`cons` `headClassifier`, the substituted head
classifier is just `RawTerm.subst (iterateLiftRaw substitution currentDepth) headClassifier`
— no universe-code brick (`subst_universeCodeCell`), unlike the formation spine
`DescTelescope.substRespectingTelescope`.  The tail's lifted substitution-condition is a
TYPING (substituents are terms that must be typed); its `0`/successor split is IDENTICAL to
the formation spine — `0` → fresh `var`, `k+1` → the substituent weakened across the binder
via the INTRINSIC `HasTypeDesc.weakenUnderBinding`.  So intrinsic eliminator-spine
substitution stands on intrinsic `HasTypeDesc` weakening.
`iterateLiftRaw σ (cd+1) ≡ RawTermSubst.lift (iterateLiftRaw σ cd)` (defeq), so a `show`
restates each lifted lookup in `lift` form and `subst_lift_weaken_commute` fires.

## Zero-axiom

Self-recursion + `HasTypeDesc.substRespectingContext` +
`HasTypeDesc.weakenUnderBinding` + the `subst_{lift_weaken_commute,
singleton_renameWeaken_cancel}` bricks.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- INTRINSIC general substitution (P6) for the eliminator-shape term spine: a
`DescTermTelescope` is preserved along any substitution whose substituents are target-typed
at the substituted source-binding types (condition stated at the spine's `currentDepth` via
`iterateLiftRaw`).  Self-recursive — the head child's typing is re-substituted by
`HasTypeDesc.substRespectingContext`; the tail recurses at depth `currentDepth + 1` with the
LIFTED substitution-condition. -/
theorem DescTermTelescope.substRespectingTermTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTermTelescope profile sourceContext children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeDesc profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTermTelescope profile targetContext
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext => fun targetContext _substitution _substitutionTyped =>
      DescTermTelescope.nil targetContext
  | .cons _sourceContext head headClassifier rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :=
          HasTypeDesc.substRespectingContext headTyped targetContext
            (iterateLiftRaw substitution currentDepth) substitutionTyped
        refine DescTermTelescope.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) headClassifier)
          (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine DescTermTelescope.substRespectingTermTelescope restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeDesc profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeDesc.var
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              ⟨0, Nat.succ_pos _⟩
        | succ k =>
            show HasTypeDesc profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth)
                ⟨k + 1, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨k + 1, indexBound⟩))
            rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
            exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)

/-- INTRINSIC single-substitution (the β-engine) for the eliminator-shape term spine:
substituting a well-typed `argument` for de Bruijn 0 throughout the children preserves
`DescTermTelescope`.  The corollary the eliminator arm's β/ι reduction cites (the scrutinee
spine's binders collapse onto the substituted argument).  Symmetric to
`DescTermTelescope.weakenUnderBinding`; mirrors `HasTypeDesc.substituteUnderBinding`'s
side-condition (`0` returns the argument after `subst_singleton_renameWeaken_cancel`, `k+1` a
shifted `var`).  `iterateLiftRaw (singleton argument) 0 ≡ singleton argument` (defeq, base
depth), so the condition reduces to the singleton-cancel handling.  INTRINSIC. -/
theorem DescTermTelescope.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {binderShifts : List Nat} {children : RawTermChildren binderShifts (scope + 1)}
    (argument : RawTerm scope)
    (telescope : DescTermTelescope profile (currentDepth := 0) (context.cons argType) children)
    (argumentTyped : HasTypeDesc profile context argument argType) :
    DescTermTelescope profile (currentDepth := 0) context
      (RawTermChildren.subst (RawTermSubst.singleton argument) children) :=
  telescope.substRespectingTermTelescope context (RawTermSubst.singleton argument) (by
    intro index
    obtain ⟨indexValue, indexBound⟩ := index
    cases indexValue with
    | zero =>
        show HasTypeDesc profile context argument
          (RawTerm.subst (RawTermSubst.singleton argument)
            (RawTerm.rename RawRenaming.weaken argType))
        rw [subst_singleton_renameWeaken_cancel]
        exact argumentTyped
    | succ k =>
        show HasTypeDesc profile context
            (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
          (RawTerm.subst (RawTermSubst.singleton argument)
            (RawTerm.rename RawRenaming.weaken
              (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
        rw [subst_singleton_renameWeaken_cancel]
        exact HasTypeDesc.var context ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)

end FX1Poly.Typed
