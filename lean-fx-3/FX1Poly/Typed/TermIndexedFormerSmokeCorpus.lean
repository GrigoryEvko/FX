import FX1Poly.Typed.BridgeFormationTermIndexedAdequacy
import FX1Poly.Typed.IdFormerTermIndexedRetrofit
import FX1Poly.Typed.HasTypeDescTermIndexedFormerStronglyNormalizing

/-! # FX1Poly/Typed/TermIndexedFormerSmokeCorpus — NATIVE-19: smoke corpus + coverage gate for the Id/Bridge engine

NATIVE-12..18 built the `HasTypeDescTermIndexedFormer` (Id/Bridge) engine and its full metatheory
(weaken/subst/inversion/uniqueness/context-conversion/SR/SN + the Id retrofit + the bridge adequacy).  This file
consolidates the non-vacuous witnesses into a coverage gate so the engine's exercised properties can NOT silently
shrink, and fills the one missing smoke (the Id strong-normalization twin of the shipped bridge one).

  * `closedIdUniverseStronglyNormalizing` — the missing Id SN smoke: `Id(Type@1, Type@0, Type@0)` is strongly
    normalizing (the Id twin of `closedBridgeUniverseStronglyNormalizing`, NATIVE-16; both via the closed SN
    headline at the respective formation witness).
  * `TermIndexedFormerEngineCoverage` + `termIndexedFormerEngineCoverageWitness` — the COVERAGE GATE: a record whose
    six fields are the engine's distinct live properties (both formers typed + strongly-normalizing, the refl
    retrofit, and the bridge standalone↔generic adequacy), inhabited by the shipped NATIVE-12..18 witnesses.  If any
    of those witnesses is deleted or renamed, the witness `def` fails to elaborate — the structural "can't silently
    shrink" guard the `#assert_namespace_min_count` macro can't provide (the engine's decls live in the shared
    `FX1Poly.Typed` namespace).

Each field references a DIFFERENT NATIVE milestone, so the single coverage def transitively certifies the whole
arc is live and zero-axiom.

## Zero-axiom

`closedIdUniverseStronglyNormalizing` is the closed SN headline at the Id formation witness; the coverage witness is
an anonymous-constructor record of the shipped witnesses.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **★ Closed Id strong normalization (the missing smoke).**  `Id(Type@1, Type@0, Type@0)` is strongly
normalizing — the Id twin of `closedBridgeUniverseStronglyNormalizing` (NATIVE-16), via the closed SN headline at
the Id formation witness `closedIdUniverseFormable` (NATIVE-17). -/
theorem closedIdUniverseStronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      ((idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0) :=
  HasTypeDescTermIndexedFormer.closedSubjectStronglyNormalizing (profile := profile)
    (closedIdUniverseFormable flag)

/-- **The term-indexed former engine coverage record.**  Each field is a distinct live property of the Id/Bridge
engine across NATIVE-12..18; an inhabitant certifies the whole arc is exercised.  Used purely as a coverage gate —
`termIndexedFormerEngineCoverageWitness` inhabits it from the shipped witnesses, so deleting any witness breaks the
build. -/
structure TermIndexedFormerEngineCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- NATIVE-12: the Bridge former is typed by the generic arm. -/
  bridgeFormerTyped : HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
    (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag)
  /-- NATIVE-16: the Bridge former is strongly normalizing. -/
  bridgeFormerSN : IsStronglyNormalizing
    ((bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0)
  /-- NATIVE-17: the Id former is typed by the generic arm. -/
  idFormerTyped : HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
    (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag)
  /-- NATIVE-19: the Id former is strongly normalizing. -/
  idFormerSN : IsStronglyNormalizing
    ((idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) : RawTerm 0)
  /-- NATIVE-17: the refl retrofit — `refl(Type@0)` inhabits `Id(Type@1, Type@0, Type@0)` AND that classifier is
  itself term-indexed-formable. -/
  reflRetrofit : HasTypeDescIdIntro profile (TypingContext.empty : TypingContext profile 0)
      (reflCell (universeCodeCell LevelExpr.lzero flag))
      (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    ∧ HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
        (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
          (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag)
  /-- NATIVE-18: the bespoke bridge engine and the generic row are inter-derivable on bridge subjects. -/
  bridgeAdequacy : HasTypeDescBridge profile (TypingContext.empty : TypingContext profile 0)
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) ↔
    HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag)

/-- **★ The coverage gate.**  Inhabits `TermIndexedFormerEngineCoverage` from the shipped NATIVE-12..18 witnesses —
deleting or renaming any of them breaks this `def`, so the term-indexed former engine's exercised property set can
NOT silently shrink.  The structural coverage gate (the engine's decls share `FX1Poly.Typed`, so a
namespace-min-count macro can't isolate them). -/
theorem termIndexedFormerEngineCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    TermIndexedFormerEngineCoverage profile flag where
  bridgeFormerTyped := termIndexedFormerGenFormation_bridgeUniverseSmoke flag
  bridgeFormerSN := closedBridgeUniverseStronglyNormalizing (profile := profile) flag
  idFormerTyped := closedIdUniverseFormable flag
  idFormerSN := closedIdUniverseStronglyNormalizing (profile := profile) flag
  reflRetrofit := reflProofWithFormableClassifier flag
  bridgeAdequacy := bridgeFormationTermIndexedAdequacy

end FX1Poly.Typed
