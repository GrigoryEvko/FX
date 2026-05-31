import FX1Poly.Typed.HasTypeDescElim
import FX1Poly.Typed.HasTypeDescWeakening

/-! # FX1Poly/Typed/HasTypeDescElimWeakening — INTRINSIC renaming/weakening (P6) for the
    ELIMINATOR-shape term spine `DescTermTelescope`.

polycell.md §11.8.5 P6 ("Substitution / weakening = whiskering, the β-engine"): typing is
preserved along a context morphism.  `DescTermTelescope` (HasTypeDescElim) is the
maximally-general typed-children spine — each child typed at an ARBITRARY classifier that
may mention all prior children — and it is the premise spine the future eliminator
`gen`-arm (the §11.8.5 non-uniform seam PAST formation) consumes.  This file ships its
renaming half: the spine is preserved along ANY renaming that respects the context, and
its weakening special case.

## Why this is the right next brick (and why it is NON-breaking)

The formation spine `DescTelescope` already has its renaming half
(`DescTelescope.renameRespectingTelescope`).  The eliminator spine did not — yet the
eliminator arm's cartesian-lift fibration leg IS exactly this lemma, regardless of how the
arm eventually lands.  Building it now does NOT touch `HasTypeDesc`'s constructors or the
`toHasType` ⟺ soundness map (no new gen rows), so it cannot disturb the shipped formation
fragment: `DescTermTelescope` is a STANDALONE inductive (`HasTypeDesc` appears only
positively in `cons`'s `headTyped`).

## Self-recursion, not a mutual block

Unlike `DescTelescope.renameRespectingTelescope` (mutual with
`HasTypeDesc.renameRespectingContext`), this is a SELF-recursive theorem: the head child's
typing is re-renamed by cross-calling the ALREADY-SHIPPED
`HasTypeDesc.renameRespectingContext` on the opaque `headTyped`, and the only recursion is
on the strictly-smaller `restTyped`.  Lean's structural recursion lands it directly (no
`termination_by`), exactly like the proven self-recursive `DescTelescope.toTermTelescope`.

## The arbitrary classifier renames generically

Because `DescTermTelescope`'s conclusion index does NOT mention the per-`cons`
`headClassifier` (it carries only the context and children), the renamed head classifier
is just `RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) headClassifier` — no
universe-code brick (`rename_universeCodeCell`) is needed.  The tail's lifted
context-condition reduces to `rename_lift_weaken_commute` on each looked-up type at every
depth, identically to the formation spine
(`iterateLiftRaw ρ (cd+1) ≡ RawRenaming.lift (iterateLiftRaw ρ cd)`, defeq).

## Zero-axiom

Self-recursion + the shipped `HasTypeDesc.renameRespectingContext` + the reused
`rename_lift_weaken_commute` brick.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- INTRINSIC renaming for the eliminator-shape term spine: a `DescTermTelescope` is
preserved along ANY renaming that respects the context (sends each source binding's
looked-up type to the target's, commuting with `rename`), with the context-condition
stated at the spine's `currentDepth` via `iterateLiftRaw`.  Self-recursive — the head
child's typing is re-renamed by the shipped `HasTypeDesc.renameRespectingContext`; the
tail recurses at depth `currentDepth + 1` with the LIFTED condition.  Decoupled from
`HasType` (the cross-call routes through the intrinsic `HasTypeDesc` renamer, not the
`⟺` soundness map). -/
theorem DescTermTelescope.renameRespectingTermTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTermTelescope profile sourceContext children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (rawRenaming : RawRenaming baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        RawTerm.rename (iterateLiftRaw rawRenaming currentDepth)
            (sourceContext.lookup index)
          = targetContext.lookup (iterateLiftRaw rawRenaming currentDepth index)) →
      DescTermTelescope profile targetContext
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil _sourceContext => fun targetContext _rawRenaming _contextCondition =>
      DescTermTelescope.nil targetContext
  | .cons _sourceContext head headClassifier rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :=
          HasTypeDesc.renameRespectingContext headTyped targetContext
            (iterateLiftRaw rawRenaming currentDepth) contextCondition
        refine DescTermTelescope.cons targetContext
          (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head)
          (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) headClassifier)
          (RawTermChildren.rename rawRenaming rest) renamedHeadTyped ?_
        refine DescTermTelescope.renameRespectingTermTelescope restTyped
          (targetContext.cons
            (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head))
          rawRenaming ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show RawTerm.rename (iterateLiftRaw rawRenaming (currentDepth + 1))
                (RawTerm.rename RawRenaming.weaken head)
              = RawTerm.rename RawRenaming.weaken
                  (RawTerm.rename (iterateLiftRaw rawRenaming currentDepth) head)
            exact rename_lift_weaken_commute
              (iterateLiftRaw rawRenaming currentDepth) head
        | succ k =>
            show RawTerm.rename (iterateLiftRaw rawRenaming (currentDepth + 1))
                (RawTerm.rename RawRenaming.weaken
                  (_sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
              = RawTerm.rename RawRenaming.weaken
                  (targetContext.lookup
                    (iterateLiftRaw rawRenaming currentDepth
                      ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
            exact (rename_lift_weaken_commute (iterateLiftRaw rawRenaming currentDepth)
                (_sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)).trans
              (congrArg (RawTerm.rename RawRenaming.weaken)
                (contextCondition ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))

/-- INTRINSIC weakening for the eliminator-shape term spine: a `DescTermTelescope` survives
extending the BASE context by one fresh binding, with the children shifted by
`RawRenaming.weaken`.  The corollary of `renameRespectingTermTelescope` whose
context-condition holds DEFINITIONALLY (`fun _ => rfl`), exactly as
`HasTypeDesc.weakenUnderBinding` does for the subject/classifier.  At base depth
(`currentDepth = 0`) `iterateLiftRaw rawRenaming 0` is the identity-lift, so `weaken index`
is `Fin.succ index` and the `cons` lookup fires its successor arm. -/
theorem DescTermTelescope.weakenUnderBinding {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {binderShifts : List Nat}
    {children : RawTermChildren binderShifts baseScope} (newBinding : RawTerm baseScope)
    (telescope : DescTermTelescope profile (currentDepth := 0) context children) :
    DescTermTelescope profile (currentDepth := 0) (context.cons newBinding)
      (RawTermChildren.rename RawRenaming.weaken children) :=
  telescope.renameRespectingTermTelescope (context.cons newBinding) RawRenaming.weaken
    (fun _ => rfl)

end FX1Poly.Typed
