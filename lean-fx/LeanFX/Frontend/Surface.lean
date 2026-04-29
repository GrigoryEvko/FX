import LeanFX.Frontend.Token
import LeanFX.Mode.Defn

namespace LeanFX.Frontend
open LeanFX.Mode

/-! # Surface syntax

`Surface scope mode sourceLength` is the parsed, not-yet-elaborated
frontend AST. Scope correctness is already intrinsic: variable nodes
carry `Fin scope`, so an out-of-scope surface variable cannot be
constructed. -/

/-- Core surface expression syntax. Later slices add declarations,
patterns, refinements, and modal annotations. -/
inductive Surface : Nat → Mode → Nat → Type
  /-- Variable reference. -/
  | var : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (position : Fin scope) →
      Surface scope mode sourceLength
  /-- Unit literal. -/
  | unit : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      Surface scope mode sourceLength
  /-- Boolean true literal. -/
  | boolTrue : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      Surface scope mode sourceLength
  /-- Boolean false literal. -/
  | boolFalse : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      Surface scope mode sourceLength
  /-- Natural zero literal. -/
  | natZero : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      Surface scope mode sourceLength
  /-- Natural successor surface form. -/
  | natSucc : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (predecessor : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Function application. -/
  | app : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (function : Surface scope mode sourceLength) →
      (argument : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Non-dependent lambda. The body sees one additional variable. -/
  | lam : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (body : Surface (scope + 1) mode sourceLength) →
      Surface scope mode sourceLength
  /-- Dependent lambda. Kept distinct so elaboration can target
  `Term.lamPi` without guessing from syntax shape alone. -/
  | lamPi : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (body : Surface (scope + 1) mode sourceLength) →
      Surface scope mode sourceLength
  /-- Pair construction. -/
  | pair : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (first : Surface scope mode sourceLength) →
      (second : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- First projection. -/
  | fst : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (pairTerm : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Second projection. -/
  | snd : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (pairTerm : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Reflexivity surface form. -/
  | refl : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (term : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Non-dependent identity eliminator surface form. -/
  | idJ : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (baseCase : Surface scope mode sourceLength) →
      (witness : Surface scope mode sourceLength) →
      Surface scope mode sourceLength

namespace Surface

/-- Extract the source span from a core surface node. -/
def spanOf {scope sourceLength : Nat} {mode : Mode} :
    Surface scope mode sourceLength → TokenSpan sourceLength
  | .var span _ => span
  | .unit span => span
  | .boolTrue span => span
  | .boolFalse span => span
  | .natZero span => span
  | .natSucc span _ => span
  | .app span _ _ => span
  | .lam span _ => span
  | .lamPi span _ => span
  | .pair span _ _ => span
  | .fst span _ => span
  | .snd span _ => span
  | .refl span _ => span
  | .idJ span _ _ => span

end Surface

namespace SmokeTestSurface

/-- One-byte span reused by constructor smoke tests. -/
def span : TokenSpan 1 :=
  SmokeTestToken.singleByteSpan

/-- Surface variable at scope one. -/
example : Surface 1 Mode.software 1 :=
  Surface.var span ⟨0, Nat.zero_lt_succ 0⟩

/-- Unit literal. -/
example : Surface 0 Mode.software 1 :=
  Surface.unit span

/-- Boolean literals. -/
example : Surface 0 Mode.software 1 :=
  Surface.boolTrue span

example : Surface 0 Mode.software 1 :=
  Surface.boolFalse span

/-- Natural literal and successor form. -/
example : Surface 0 Mode.software 1 :=
  Surface.natSucc span (Surface.natZero span)

/-- Application form. -/
example : Surface 0 Mode.software 1 :=
  Surface.app span (Surface.unit span) (Surface.unit span)

/-- Lambda forms with a scoped variable in the body. -/
example : Surface 0 Mode.software 1 :=
  Surface.lam span (Surface.var span ⟨0, Nat.zero_lt_succ 0⟩)

example : Surface 0 Mode.software 1 :=
  Surface.lamPi span (Surface.var span ⟨0, Nat.zero_lt_succ 0⟩)

/-- Pair and projections. -/
example : Surface 0 Mode.software 1 :=
  Surface.pair span (Surface.unit span) (Surface.boolTrue span)

example : Surface 0 Mode.software 1 :=
  Surface.fst span (Surface.pair span (Surface.unit span) (Surface.boolTrue span))

example : Surface 0 Mode.software 1 :=
  Surface.snd span (Surface.pair span (Surface.unit span) (Surface.boolTrue span))

/-- Identity forms. -/
example : Surface 0 Mode.software 1 :=
  Surface.refl span (Surface.boolTrue span)

example : Surface 0 Mode.software 1 :=
  Surface.idJ span (Surface.unit span) (Surface.refl span (Surface.boolTrue span))

/-- Span extraction returns the constructor span. -/
example :
    Surface.spanOf (Surface.unit (scope := 0) (mode := Mode.software) span) = span :=
  rfl

end SmokeTestSurface

end LeanFX.Frontend
