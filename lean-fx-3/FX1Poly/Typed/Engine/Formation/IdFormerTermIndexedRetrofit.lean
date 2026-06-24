import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations

/-! # FX1Poly/Typed/IdFormerTermIndexedRetrofit — NATIVE-17: the Id retrofit

The identity type former `Id(A, a, b)` predates the term-indexed table: the value engine `HasTypeDescIdIntro`
(DI-2d) types `refl(x) : Id(A, x, x)` at the `idTypeCell` classifier, but the FORMATION of `Id(A, a, b)` itself
had no native rule (NATIVE-12's docstring: "NO bespoke `idFormation` rule anywhere").  NATIVE-12 made `gen_idCode`
a row in `termIndexedFormerDescOf`, so the Id former is now typed by the SAME generic arm as `Bridge`.  This file
RETROFITS the existing Id story onto that arm — and after TABLE-CANON-6 the arm is the union's own
`formationRule` table arm (term-indexed family) (the standalone `HasTypeDescTermIndexedFormer` engine that
NATIVE-12 seeded was retired once the union inlined it), so the retrofit types `Id` directly in the unified
judgment:

  * **idCode formable** — `idFormationViaTermIndexed` reads `termIndexedFormerDescOf`'s `gen_idCode` row and
    consumes the term-indexed telescope (carrier `A : Type@e`, endpoints `a, b : A`) to type the canonical
    `idTypeCell` cell (definitionally `mkGen gen_idCode () [A, a, b]`): `Id(A, a, b) : Type@e`.
    `closedIdUniverseFormable` is the closed witness `Id(Type@1, Type@0, Type@0) : Type@2`.
  * **refl classifier formable** — `reflClassifierTermIndexedFormable` shows the EXACT classifier
    `Id(A, x, x)` that `HasTypeDescIdIntro.reflIntro` produces is term-indexed-formable (the reflexive instance,
    both endpoints the witness), given the witness type `A : Type@e`.  `reflProofWithFormableClassifier` is the
    capstone: `refl(Type@0) : Id(Type@1, Type@0, Type@0)` AND that classifier is itself formable at `Type@2`
    through the unified engine — the refl value and the formation of the type it inhabits now both route through
    the SAME `HasTypeUnion` judgment (the refl value through the union's reflexive data-intro arm, the type
    through the union's term-indexed-former table arm).

This is the adequacy the Id former needed: `refl`'s classifier is no longer a free-floating `idTypeCell`; it is a
cell the kernel can FORM and (NATIVE-16) strongly normalize.

## Zero-axiom

`idFormationViaTermIndexed` is a direct `HasTypeUnion.formationRuleOfObligations` application (term-indexed family) at the
`gen_idCode` row (the output `termIndexedCarrierOutput … = universeCodeCell …` collapses by `rfl`, the `idTypeCell` cell IS
`mkGen gen_idCode () (childCons …)` definitionally; the three term-indexed obligations — carrier at `Type@e`, both
endpoints at the carrier — are discharged by structural `cases` on the obligation-list membership, no host bridge);
`reflClassifierTermIndexedFormable` instantiates it at equal endpoints; the closed witnesses are direct applications over
native `HasTypeUnion.universeFormation` sub-derivations; the
capstone is an anonymous pair.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ idCode formable.**  `Id(A, a, b) : Type@e` through the union's term-indexed-former table arm, phrased in
the canonical `idTypeCell` builder (definitionally the `gen_idCode` cell `mkGen gen_idCode () [A, a, b]`).  The Id
former IS the generic `formationRule` arm (term-indexed family) at the `gen_idCode` row — carrier `A : Type@e`, endpoints
`a, b : A`, output the carrier's universe `Type@e`. -/
theorem idFormationViaTermIndexed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrier left right : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (carrierTyped : HasTypeUnion profile context carrier (universeCodeCell level flag))
    (leftTyped : HasTypeUnion profile context left carrier)
    (rightTyped : HasTypeUnion profile context right carrier) :
    HasTypeUnion profile context (idTypeCell carrier left right)
      (universeCodeCell level flag) :=
  HasTypeUnion.formationRuleOfObligations context .gen_idCode ()
    (.childCons carrier (.childCons left (.childCons right .childNil)))
    (.termIndexed { outputType := termIndexedCarrierOutput })
    [] carrier level flag rfl
    (fun _obligation hmem => by
      cases hmem with
      | head => exact carrierTyped
      | tail _ hmemLeft =>
        cases hmemLeft with
        | head => exact leftTyped
        | tail _ hmemRight =>
          cases hmemRight with
          | head => exact rightTyped
          | tail _ hmemEmpty => cases hmemEmpty)

/-- **★ refl classifier formable.**  The EXACT classifier `Id(A, x, x)` that
`HasTypeDescIdIntro.reflIntro` produces (the reflexive identity type, both endpoints the witness) is
term-indexed-formable, given the witness type `A : Type@e`.  `refl`'s classifier is therefore a kernel-formable
cell — the formation of the identity type a reflexivity proof inhabits is native, not a free-floating
`idTypeCell`. -/
theorem reflClassifierTermIndexedFormable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (witness typeCode : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (typeCodeTyped : HasTypeUnion profile context typeCode (universeCodeCell level flag))
    (witnessTyped : HasTypeUnion profile context witness typeCode) :
    HasTypeUnion profile context (idTypeCell typeCode witness witness)
      (universeCodeCell level flag) :=
  idFormationViaTermIndexed typeCode witness witness level flag typeCodeTyped witnessTyped witnessTyped

/-- **★ Closed witness: idCode formable.**  `Id(Type@1, Type@0, Type@0) : Type@2` through the union's
term-indexed-former arm (carrier `Type@1 : Type@2`, endpoints `Type@0 : Type@1` members of the carrier). -/
theorem closedIdUniverseFormable {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  idFormationViaTermIndexed (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    (HasTypeUnion.universeFormation TypingContext.empty (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeUnion.universeFormation TypingContext.empty LevelExpr.lzero flag)
    (HasTypeUnion.universeFormation TypingContext.empty LevelExpr.lzero flag)

/-- **★ The Id retrofit capstone.**  `refl(Type@0)` inhabits the reflexive identity type
`Id(Type@1, Type@0, Type@0)` (via the UNION's reflexive data-intro arm at the `gen_refl` row — the
NATIVE-42 re-base of the retired bespoke `HasTypeDescIdIntro` premise), AND that classifier is itself
formable at `Type@2` through the union's term-indexed-former arm — the reflexivity VALUE and the FORMATION
of the identity type it inhabits both route through the SAME unified `HasTypeUnion` judgment.  The closed
demonstration that `refl`'s classifier is union-formable. -/
theorem reflProofWithFormableClassifier {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
        (reflCell (universeCodeCell LevelExpr.lzero flag))
        (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
          (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      ∧ HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
          (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
            (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  ⟨HasTypeUnion.intro TypingContext.empty .gen_refl reflIntroRule
      (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil)
      (.childCons (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) .childNil)
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial
      (fun obligation hmem => by
        cases hmem with
        | head =>
          exact HasTypeUnion.universeFormation TypingContext.empty LevelExpr.lzero flag
        | tail _ hmem => cases hmem),
   closedIdUniverseFormable flag⟩

end FX1Poly.Typed
