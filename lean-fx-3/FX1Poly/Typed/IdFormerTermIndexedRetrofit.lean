import FX1Poly.Typed.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.HasTypeDescIdIntro

/-! # FX1Poly/Typed/IdFormerTermIndexedRetrofit — NATIVE-17: the Id retrofit

The identity type former `Id(A, a, b)` predates the term-indexed table: the value engine `HasTypeDescIdIntro`
(DI-2d) types `refl(x) : Id(A, x, x)` at the `idTypeCell` classifier, but the FORMATION of `Id(A, a, b)` itself
had no native rule (NATIVE-12's docstring: "NO bespoke `idFormation` rule anywhere").  NATIVE-12 made `gen_idCode`
a row in `termIndexedFormerDescOf`, so the Id former is now typed by the SAME generic arm as `Bridge`.  This file
RETROFITS the existing Id story onto that engine:

  * **idCode formable** — `idFormationViaTermIndexed` recasts `termIndexedFormerGenFormation_idCode` in the
    canonical `idTypeCell` builder (definitionally the `gen_idCode` cell): `Id(A, a, b) : Type@e` whenever the
    carrier `A : Type@e` and the endpoints `a, b : A`.  `closedIdUniverseFormable` is the closed witness
    `Id(Type@1, Type@0, Type@0) : Type@2`.
  * **refl classifier grown-formable** — `reflClassifierTermIndexedFormable` shows the EXACT classifier
    `Id(A, x, x)` that `HasTypeDescIdIntro.reflIntro` produces is term-indexed-formable (the reflexive instance,
    both endpoints the witness), given the witness type `A : Type@e`.  `reflProofWithFormableClassifier` is the
    capstone: `refl(Type@0) : Id(Type@1, Type@0, Type@0)` AND that classifier is itself formable at `Type@2`
    through the unified engine — the refl value and the formation of the type it inhabits now both route through
    native rules (the value through `HasTypeDescIdIntro`, the type through the term-indexed table).

This is the adequacy the Id former needed: `refl`'s classifier is no longer a free-floating `idTypeCell`; it is a
cell the kernel can FORM and (NATIVE-16) strongly normalize.

## Zero-axiom

`idFormationViaTermIndexed` is `termIndexedFormerGenFormation_idCode` at the `idTypeCell` builder (defeq);
`reflClassifierTermIndexedFormable` instantiates it at equal endpoints; the closed witnesses are direct
applications over `ofFormation universeFormation` sub-derivations; the capstone is an anonymous pair.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ idCode formable.**  `Id(A, a, b) : Type@e` through the term-indexed former engine, phrased in the
canonical `idTypeCell` builder (definitionally the `gen_idCode` cell `termIndexedFormerGenFormation_idCode`
produces).  The Id former IS the generic arm at the `gen_idCode` row — carrier `A : Type@e`, endpoints `a, b : A`,
output the carrier's universe `Type@e`. -/
theorem idFormationViaTermIndexed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrier left right : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (carrierTyped : HasTypeDescPi profile context carrier (universeCodeCell level flag))
    (leftTyped : HasTypeDescPi profile context left carrier)
    (rightTyped : HasTypeDescPi profile context right carrier) :
    HasTypeDescTermIndexedFormer profile context (idTypeCell carrier left right)
      (universeCodeCell level flag) :=
  termIndexedFormerGenFormation_idCode carrier left right level flag carrierTyped leftTyped rightTyped

/-- **★ refl classifier grown-formable.**  The EXACT classifier `Id(A, x, x)` that
`HasTypeDescIdIntro.reflIntro` produces (the reflexive identity type, both endpoints the witness) is
term-indexed-formable, given the witness type `A : Type@e`.  `refl`'s classifier is therefore a kernel-formable
cell — the formation of the identity type a reflexivity proof inhabits is native, not a free-floating
`idTypeCell`. -/
theorem reflClassifierTermIndexedFormable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (witness typeCode : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (typeCodeTyped : HasTypeDescPi profile context typeCode (universeCodeCell level flag))
    (witnessTyped : HasTypeDescPi profile context witness typeCode) :
    HasTypeDescTermIndexedFormer profile context (idTypeCell typeCode witness witness)
      (universeCodeCell level flag) :=
  idFormationViaTermIndexed typeCode witness witness level flag typeCodeTyped witnessTyped witnessTyped

/-- **★ Closed witness: idCode formable.**  `Id(Type@1, Type@0, Type@0) : Type@2` through the term-indexed
engine (carrier `Type@1 : Type@2`, endpoints `Type@0 : Type@1` members of the carrier). -/
theorem closedIdUniverseFormable {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
      (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  idFormationViaTermIndexed (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty (LevelExpr.lsucc LevelExpr.lzero) flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ The Id retrofit capstone.**  `refl(Type@0)` inhabits the reflexive identity type
`Id(Type@1, Type@0, Type@0)` (via `HasTypeDescIdIntro`), AND that classifier is itself formable at `Type@2`
through the term-indexed engine — the reflexivity VALUE and the FORMATION of the identity type it inhabits both
route through native rules.  The closed demonstration that `refl`'s classifier is grown-formable. -/
theorem reflProofWithFormableClassifier {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescIdIntro profile (TypingContext.empty : TypingContext profile 0)
        (reflCell (universeCodeCell LevelExpr.lzero flag))
        (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
          (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      ∧ HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
          (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
            (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  ⟨HasTypeDescIdIntro.reflOfUniverseCodeTyped flag, closedIdUniverseFormable flag⟩

end FX1Poly.Typed
