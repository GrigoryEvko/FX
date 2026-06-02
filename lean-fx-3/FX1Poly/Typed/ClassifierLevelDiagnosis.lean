import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Typed.HasType
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Typed/ClassifierLevelDiagnosis
    — SN-002 spike: can the reducibility level BE the classifier universe level `denote(LevelExpr)`?

`ReducibleTypeAt`/`IsReducibleMemberAt` are indexed by an external `Nat` "fuel" level, and SN-001
(`RouteAObstruction`) pinned why that fuel model is defective at its base (fuel-0 universe membership is
empty, so a universe-domain Π is vacuously reducible at fuel 0).  SN-002 diagnoses whether the cure is to
RE-KEY that `Nat` to the type's CLASSIFIER universe level `denote(LevelExpr)` rather than depth.  Findings,
backed by the concrete probe below:

* **`LevelExpr.denote : LevelExpr → (Nat → Nat) → Nat` is ENV-parameterized.**  The `lvar idx` arm reads
  `env idx`, so the classifier "universe level" is a concrete `Nat` only after fixing a universe-variable
  environment `env`.  Closed levels (no `lvar`) are env-independent; universe-POLYMORPHIC types must thread
  `env`.  This is a real wrinkle for the reformulation, not a blocker (fix `env` at the top, or quantify).

* **The classifier successor aligns with the reducibility `+1`.**  `LevelExpr.denote_lsucc` (rfl) gives
  `denote (lsucc e) env = denote e env + 1`.  So a member of `Type@e` sits exactly ONE denoted level below
  its classifier `Type@(lsucc e)` — matching the shipped `tarskiDecode` / `tarskiEncode` discipline
  (`member @ (L+1) ↔ reducible-type @ L`) on the nose.  The denote measure is therefore COHERENT with the
  existing universe arm.

* **The universe-formation arm serves cleanly under denote-keying.**  `universeCode_reducibleMemberAtClassifierLevel`
  (below) proves `Type@e` IS a reducible member of `Type@(lsucc e)` at the DENOTED classifier level
  `denote (lsucc e) env`, by instantiating the shipped `IsReducibleMemberAt.universeFormation` at
  `predLevel := denote e env` — the `+1`/`lsucc` alignment makes this hold by definitional equality (no
  rewrite).  Concrete evidence that re-keying the level to the classifier denotation is well-formed.

* **It is an INSTANTIATION, not a rebuild.**  The shipped `FundamentalConclusionLevelIndexed contextLevels
  subjectLevel` is level-POLYMORPHIC — `contextLevels : Fin scope → Nat` and `subjectLevel : Nat` are
  arbitrary naturals.  "Classifier-level reducibility" is just the choice
  `contextLevels := fun i => denote (classifierOf i) env`, `subjectLevel := denote (classifierOf subject) env`;
  the per-binder level annotation that supplies `classifierOf` already exists (`ValidTyping`, SN-007).  No
  new relation is required — only the choice of level values.

* **GO (setup) / make-or-break deferred.**  Verdict for SN-002: the denote-keyed setup is COHERENT (an
  lsucc-aligned `Nat` measure, served by the universe arm, instantiable in the existing relation), so the
  reformulation is worth pursuing.  Whether it DISSOLVES the `∀ aboveLevel` universe-DOMAIN Π-formation
  premise that SN-001 pinned as the fuel defect — the only thing that would beat the shipped fuel-level
  leveling bridge (SN-022) — is the make-or-break, deferred to SN-004.  SN-003 next lands the predicative
  well-founded measure (`denote e env < denote (lsucc e) env`) the denote-keyed recursion needs.

## Zero-axiom verification

The probe theorem is the shipped `IsReducibleMemberAt.universeFormation` applied at a denote-derived level,
closing by definitional equality (`denote_lsucc` is `rfl`; no `rw`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **SN-002 probe: the universe code is reducible at its DENOTED classifier level.**  `Type@e` is a
reducible member of its classifier `Type@(lsucc e)` at the level `denote (lsucc e) env` — the universe
level of the classifier under any universe-variable environment `env`.  Proof: the shipped
`IsReducibleMemberAt.universeFormation` produces membership at `predLevel + 1`; taking
`predLevel := denote e env` and using `denote (lsucc e) env = denote e env + 1` (definitional via
`denote_lsucc`) lands it at exactly the denoted classifier level — no rewrite, no propext.  This is the
concrete evidence that re-keying the reducibility level from external fuel to the classifier denotation is
well-formed for the universe-formation arm (the SN-002 setup verdict; the make-or-break Π-formation case is
SN-004). -/
theorem universeCode_reducibleMemberAtClassifierLevel {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (env : Nat → Nat) :
    IsReducibleMemberAt (scope := scope) (LevelExpr.denote levelExpr.lsucc env)
      (universeCodeCell levelExpr.lsucc flag) (universeCodeCell levelExpr flag) :=
  IsReducibleMemberAt.universeFormation (LevelExpr.denote levelExpr env) levelExpr flag

end FX1Poly.Typed
