import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion
import FX1Poly.Typed.IsTypeDescRigidity
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/IsTypeDescDecidableGeneric
    — the FULLY CASCADE-FREE native `IsTypeDesc` decider

The cascade-free type-hood decider, a STRUCTURAL MUTUAL recursion over the `RawTerm` / `RawTermChildren` mutual
inductive (no size measure, no `termination_by`).  Dispatching `typingRuleDescOf` directly avoids the cascade
trap that hand-written Π / Σ branches + a `typingRuleDescOf_isPiOrSigma` `else` would have: a new formation row
(`listCode`/`optionCode`/…) is absorbed with no new branch and no `else` to break:

  * `IsTypeDesc.decideTypeGeneric` — decides any `mkGen` classifier: `universeCode` ⇒ type (leaf);
    `var` ⇒ type iff the lookup is a universe code (leaf); ANY OTHER head dispatches `typingRuleDescOf`
    directly — `some` routes the children through `decideSynthGeneric` and reassembles via the generic
    `genFormation` arm, `none` refutes via `not_of_rootGenerator`.  Names NO formation generator.
  * `DescTelescope.decideSynthGeneric` — the flag-synthesizing telescope decider: peeks the head
    (`decideTypeGeneric`) to fix the shared flag, then decides the TAIL at that flag via `decideAtFlagGeneric`
    and reassembles the `cons` (the ASSEMBLE form — recurses on the strict subterm `childTail`, never the whole
    children, so the mutual recursion stays structural).
  * `DescTelescope.decideAtFlagGeneric` — the cascade-free fixed-flag telescope decider, deciding each child a
    type at the shared flag via `decideTypeGeneric`.

A future formation row is absorbed with ZERO new arms — the extensibility property realized for the decider
itself, so a new type code (e.g. `listCode`) lands into `typingRuleDescOf` zero-touch.

## Zero-axiom verification

STRUCTURAL mutual recursion (the `RawTerm`/`RawTermChildren` subterm order — every recursive call sits on a
syntactic child).  The `subst hShift` in the spine deciders eliminates `currentDepth` (NOT `childHead`'s
`shift`), so it does not obscure the recursive argument — the same discipline as the shipped `decideAtFlag`.
The leaf `inl` witnesses are the formation constructors; the `inr` refutations compose the native inversions +
`HasTypeDesc.uniqueness` + `universeCodeCell_inj_of_conv` + `not_of_rootGenerator`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual

/-- **The cascade-free `IsTypeDesc` decision core.**  `universeCode` / `var` leaves verbatim from
`decideWithWitness`; any other head dispatches `typingRuleDescOf` (no Π / Σ enumeration) — `some` synthesises the
children telescope (`decideSynthGeneric`) and reassembles the former via the generic `genFormation`, `none`
refutes via `not_of_rootGenerator`. -/
def IsTypeDesc.decideTypeGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (classifier : RawTerm scope) :
    PSum
      (Σ' (levelExpr : LevelExpr) (flag : UniverseFlag),
        HasTypeDesc profile context classifier (universeCodeCell levelExpr flag))
      (IsTypeDesc profile context classifier → False) :=
  match classifier with
  | .mkGen generator payload children =>
      if hUniverse : generator = Generator.gen_universeCode then by
        subst hUniverse
        have cellIsUniverseCode :
            (RawTerm.mkGen Generator.gen_universeCode payload children)
              = universeCodeCell payload.1 payload.2 := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact .inl ⟨payload.1.lsucc, payload.2, by
          rw [cellIsUniverseCode]
          exact HasTypeDesc.universeFormation context payload.1 payload.2⟩
      else if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children) = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact match hLookupCell : context.lookup payload with
          | .mkGen lookupGenerator lookupPayload lookupChildren =>
              if hLookupUniverse : lookupGenerator = Generator.gen_universeCode then by
                subst hLookupUniverse
                have lookupIsUniverseCode :
                    context.lookup payload
                      = universeCodeCell lookupPayload.1 lookupPayload.2 := by
                  rw [hLookupCell, RawTermChildren.eq_childNil lookupChildren]; rfl
                exact .inl ⟨lookupPayload.1, lookupPayload.2, by
                  rw [cellIsVariable, ← lookupIsUniverseCode]
                  exact HasTypeDesc.var context payload⟩
              else by
                exact .inr (by
                  rw [cellIsVariable]
                  intro isTypeVariable
                  have headIsUniverse :
                      RawTerm.headGenerator (context.lookup payload)
                        = Generator.gen_universeCode :=
                    (IsTypeDesc.variableCell_iff_lookupIsUniverseCode
                      wellFormed payload).mp isTypeVariable
                  rw [hLookupCell] at headIsUniverse
                  exact hLookupUniverse headIsUniverse)
      else by
        exact (match hGen : typingRuleDescOf generator with
          | some rule =>
              match DescTelescope.decideSynthGeneric (currentDepth := 0) context wellFormed children with
              | .inl ⟨flag, levels, telescope⟩ =>
                  -- The `.inl` Σ' is TYPE-valued and must EXHIBIT a concrete (level, flag) as data;
                  -- `typingRuleDescOf_output_isUniverseCode` only ASSERTS existence (a Prop `∃`, which
                  -- cannot eliminate into the Σ'/PSum), so the constructive witnesses come from the
                  -- COMPUTABLE row-data accessor `formationOutputData` — uniform across the flag-using
                  -- and the flag-pinned nullary row shapes.
                  .inl ⟨(formationOutputData generator levels flag).1,
                    (formationOutputData generator levels flag).2, by
                    have formerTyped :=
                      HasTypeDesc.genFormation context generator payload children levels flag rule hGen telescope
                    rw [typingRuleDescOf_output_eq_outputData hGen] at formerTyped
                    exact formerTyped⟩
              | .inr noTelescopeAtAnyFlag =>
                  .inr (fun isType => by
                    obtain ⟨_levelExpr, _flag, typed⟩ := isType
                    obtain ⟨levels, telFlag, telescope, _convToCode⟩ :=
                      HasTypeDesc.inversionFormerWithConvGeneric typed hGen rfl
                    exact noTelescopeAtAnyFlag telFlag levels telescope)
          | none => .inr (IsTypeDesc.not_of_rootGenerator hVariable hUniverse hGen))

/-- **Flag-synthesizing telescope decider (ASSEMBLE form, mutual).**  `childNil` ⇒ telescope at `.standard`;
`childCons` peeks the head via `decideTypeGeneric` (its binder shift must equal the depth), fixes the shared flag
to the head's, decides the TAIL at that flag via `decideAtFlagGeneric`, and reassembles the `cons`.  Recurses on
the strict subterm `childTail` (never the whole children), so the mutual recursion is structural. -/
def DescTelescope.decideSynthGeneric {profile : PolyProfile} {baseScope : Nat} :
    {currentDepth : Nat} → {binderShifts : List Nat} →
    (context : TypingContext profile (baseScope + currentDepth)) →
    WfContextDesc context →
    (children : RawTermChildren binderShifts baseScope) →
    PSum
      (Σ' flag : UniverseFlag, Σ' levels : List LevelExpr,
        DescTelescope profile (currentDepth := currentDepth) context levels flag children)
      ((flag : UniverseFlag) → (levels : List LevelExpr) →
        DescTelescope profile (currentDepth := currentDepth) context levels flag children → False)
  | _currentDepth, _, context, _wellFormed, .childNil =>
      .inl ⟨UniverseFlag.standard, [], DescTelescope.nil context UniverseFlag.standard⟩
  | currentDepth, _, context, wellFormed,
      @RawTermChildren.childCons _ shift _ childHead childTail =>
      if hShift : shift = currentDepth then by
        subst hShift
        exact (match IsTypeDesc.decideTypeGeneric wellFormed childHead with
          | .inr headNotType =>
              .inr (fun flag _levels telescope => by
                cases telescope with
                | cons _ctx _hd headLevel _rl _fl _rst headTyped _rt =>
                    exact headNotType ⟨headLevel, flag, headTyped⟩)
          | .inl ⟨headLevel, headFlag, headTyped⟩ =>
              match DescTelescope.decideAtFlagGeneric headFlag
                  (currentDepth := shift + 1) (context.cons childHead)
                  (WfContextDesc.cons wellFormed ⟨headLevel, headFlag, headTyped⟩) childTail with
              | .inl ⟨restLevels, restTelescope⟩ =>
                  .inl ⟨headFlag, headLevel :: restLevels,
                    DescTelescope.cons context childHead headLevel restLevels headFlag childTail
                      headTyped restTelescope⟩
              | .inr restRefutes =>
                  .inr (fun _flag _levels telescope => by
                    cases telescope with
                    | cons _ctx _hd _telHeadLevel restLevels _flg _rst telHeadTyped restTyped =>
                        obtain ⟨_, flagAgree⟩ :=
                          universeCodeCell_inj_of_conv
                            (HasTypeDesc.uniqueness telHeadTyped wellFormed headTyped)
                        subst flagAgree
                        exact restRefutes restLevels restTyped))
      else
        .inr (fun _flag _levels telescope => by
          cases telescope with
          | cons _ctx _hd _headLevel _restLevels _flg _rst _headTyped _restTyped =>
              exact hShift rfl)

/-- **Fixed-flag telescope decider (mutual).**  The cascade-free twin of `decideAtFlag`: decides whether
`children` form a telescope at the given `flag`, deciding each child a type at `flag` via `decideTypeGeneric`.
`subst hShift` eliminates `currentDepth` (safe — not in `childHead`'s type), keeping the recursion structural. -/
def DescTelescope.decideAtFlagGeneric {profile : PolyProfile} {baseScope : Nat}
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
        exact (match IsTypeDesc.decideTypeGeneric wellFormed childHead with
          | .inr headNotType =>
              .inr (fun _levels telescope => by
                cases telescope with
                | cons _ctx _hd headLevel _restLevels _flg _rst headTyped _restTyped =>
                    exact headNotType ⟨headLevel, flag, headTyped⟩)
          | .inl ⟨headLevel, headFlag, headTyped⟩ =>
              if hFlag : headFlag = flag then by
                subst headFlag
                exact (match DescTelescope.decideAtFlagGeneric flag
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
                          (HasTypeDesc.uniqueness headTyped wellFormed telHeadTyped)
                      exact hFlag flagAgree))
      else
        .inr (fun _levels telescope => by
          cases telescope with
          | cons _ctx _hd _headLevel _restLevels _flg _rst _headTyped _restTyped =>
              exact hShift rfl)

end

/-- **Native cascade-free `Decidable (IsTypeDesc Γ T)`.**  The typeclass form of the structural mutual decider:
the `Type`-valued `decideTypeGeneric` witness PSum becomes the `Prop`-valued `Decidable` (the `.inl` universe
witness is `isTrue`, the `.inr` refutation is `isFalse`).  The cascade-free twin of
`IsTypeDesc.decidableOfWellFormed` (which routes through the Π/Σ-enumerating `decideWithWitness`): this one
decides ANY classifier with NO `typingRuleDescOf_isPiOrSigma` enumeration, so a future formation row is absorbed
zero-touch.  The canonical decidability for the formation type-hood judgment. -/
def IsTypeDesc.decidableOfWellFormedGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (classifier : RawTerm scope) : Decidable (IsTypeDesc profile context classifier) :=
  match IsTypeDesc.decideTypeGeneric wellFormed classifier with
  | .inl ⟨levelExpr, flag, typed⟩ => isTrue ⟨levelExpr, flag, typed⟩
  | .inr notType => isFalse notType

end FX1Poly.Typed
