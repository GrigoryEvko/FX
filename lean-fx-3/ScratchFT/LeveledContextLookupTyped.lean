import FX1Poly.Typed.LeveledContext
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeWeakening

/-! Scratch: `LeveledContext.lookupTyped` — every entry of a leveled context is a HasTypeDescPi-type at a
universe code, in the FULL context (not just its prefix). This is the substrate the totalBridge's var/conv
arms consume: they need to know each looked-up context variable is universe-classified (the
`reclassifierIsUniverse : context.lookup index = universeCodeCell ..` premise of
`validTypingBridgeConvPinnedReclassifier`, and the formation reading the var arm performs).

Proof: leveled-context recursor (clean, like `allLevelsPositive`); the per-position `Fin` split is a
propext-clean `⟨0,_⟩` / `⟨k+1,_⟩` structure match. The head entry's prefix typing (`bindingTyped`) and each
tail entry's typing (IH) are weakened into the full context by `HasTypeDescPi.weakenUnderBinding`; the classifier
`universeCodeCell ..` is rename-invariant (`rename_universeCodeCell`, rfl), and the lookup is unfolded by
`lookup_cons_zero` / `lookup_cons_succ` (both rfl) to exactly the weakened term. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem LeveledContext.lookupTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {contextLevels : Fin scope → Nat}
    (leveled : LeveledContext profile context contextLevels) :
    ∀ index : Fin scope, ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      HasTypeDescPi profile context (context.lookup index) (universeCodeCell levelExpr flag) := by
  induction leveled with
  | empty => exact fun index => index.elim0
  | @cons scope context contextLevels bindingType levelExpr flag predLevel _rest bindingTyped tailLookup =>
      intro index
      match index with
      | ⟨0, isLtZeroSucc⟩ =>
          refine ⟨levelExpr, flag, ?_⟩
          rw [TypingContext.lookup_cons_zero context bindingType isLtZeroSucc]
          have weakened := bindingTyped.weakenUnderBinding bindingType
          rw [rename_universeCodeCell] at weakened
          exact weakened
      | ⟨position + 1, isLtSuccSucc⟩ =>
          obtain ⟨entryLevelExpr, entryFlag, entryTyped⟩ :=
            tailLookup ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩
          refine ⟨entryLevelExpr, entryFlag, ?_⟩
          rw [TypingContext.lookup_cons_succ context bindingType position isLtSuccSucc]
          have weakened := entryTyped.weakenUnderBinding bindingType
          rw [rename_universeCodeCell] at weakened
          exact weakened

end FX1Poly.Typed

#print axioms FX1Poly.Typed.LeveledContext.lookupTyped
