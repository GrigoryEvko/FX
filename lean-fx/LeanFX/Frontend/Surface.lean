import LeanFX.Frontend.Token
import LeanFX.Mode.Defn

namespace LeanFX.Frontend
open LeanFX.Mode

/-! # Surface syntax

`Surface scope mode sourceLength` is the parsed, not-yet-elaborated
frontend AST. Scope correctness is already intrinsic: variable nodes
carry `Fin scope`, so an out-of-scope surface variable cannot be
constructed. -/

/-- A source-spanned name. -/
structure NameSpan (sourceLength : Nat) where
  span : TokenSpan sourceLength
  text : String
deriving DecidableEq

/-- Surface binding prefixes before elaboration into kernel modes and grades. -/
inductive BindingPrefix where
  | linear
  | affine
  | own
  | ref
  | refMut
  | ghost
deriving DecidableEq

/- Core surface expression syntax. Later slices add declarations,
patterns, refinements, and modal annotations. -/
mutual

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
  /-- Let binding. The body sees the newly-bound value. -/
  | letBind : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (param : ParamData scope mode sourceLength) →
      (rhs : Surface scope mode sourceLength) →
      (body : Surface (scope + 1) mode sourceLength) →
      Surface scope mode sourceLength
  /-- Function declaration as a surface expression node for the bootstrap frontend. -/
  | fnDecl : {scope sourceLength : Nat} → {mode : Mode} →
      {paramCount : Nat} →
      (span : TokenSpan sourceLength) →
      (name : NameSpan sourceLength) →
      (params : ParamList paramCount scope mode sourceLength) →
      (returnType : Surface scope mode sourceLength) →
      (body : Surface (scope + paramCount) mode sourceLength) →
      Surface scope mode sourceLength
  /-- Type ascription. -/
  | ascribe : {scope sourceLength : Nat} → {mode : Mode} →
      (span : TokenSpan sourceLength) →
      (expression : Surface scope mode sourceLength) →
      (annotation : Surface scope mode sourceLength) →
      Surface scope mode sourceLength
  /-- Multi-parameter lambda, elaborated later into nested lambdas. -/
  | lamMulti : {scope sourceLength : Nat} → {mode : Mode} →
      {paramCount : Nat} →
      (span : TokenSpan sourceLength) →
      (params : ParamList paramCount scope mode sourceLength) →
      (body : Surface (scope + paramCount) mode sourceLength) →
      Surface scope mode sourceLength

/-- Surface parameter data. Type annotations are themselves surface
syntax because FX has a unified type/expression grammar. -/
inductive ParamData : Nat → Mode → Nat → Type
  | mk : {scope sourceLength : Nat} → {mode : Mode} →
      (name : NameSpan sourceLength) →
      (bindingPrefix : BindingPrefix) →
      (typeAnnotation : Surface scope mode sourceLength) →
      ParamData scope mode sourceLength

/-- Parameter lists indexed by length to avoid nested `List` inside the
mutual frontend AST. -/
inductive ParamList : Nat → Nat → Mode → Nat → Type
  | nil : {scope sourceLength : Nat} → {mode : Mode} →
      ParamList 0 scope mode sourceLength
  | cons : {count scope sourceLength : Nat} → {mode : Mode} →
      (head : ParamData scope mode sourceLength) →
      (tail : ParamList count scope mode sourceLength) →
      ParamList (count + 1) scope mode sourceLength

end

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
  | .letBind span _ _ _ => span
  | .fnDecl span _ _ _ _ => span
  | .ascribe span _ _ => span
  | .lamMulti span _ _ => span

end Surface

namespace SmokeTestSurface

/-- One-byte span reused by constructor smoke tests. -/
def span : TokenSpan 1 :=
  SmokeTestToken.singleByteSpan

/-- A one-byte surface name. -/
def name : NameSpan 1 where
  span := span
  text := "x"

/-- A parameter with a unit type annotation. -/
def unitParam : ParamData 0 Mode.software 1 :=
  ParamData.mk name BindingPrefix.linear (Surface.unit span)

/-- A one-parameter list. -/
def oneUnitParam : ParamList 1 0 Mode.software 1 :=
  ParamList.cons unitParam ParamList.nil

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

/-- Let binding with one additional body variable. -/
example : Surface 0 Mode.software 1 :=
  Surface.letBind span unitParam (Surface.unit span)
    (Surface.var span ⟨0, Nat.zero_lt_succ 0⟩)

/-- Function declaration with one parameter. -/
example : Surface 0 Mode.software 1 :=
  Surface.fnDecl span name oneUnitParam (Surface.unit span)
    (Surface.var span ⟨0, Nat.zero_lt_succ 0⟩)

/-- Type ascription. -/
example : Surface 0 Mode.software 1 :=
  Surface.ascribe span (Surface.unit span) (Surface.unit span)

/-- Multi-parameter lambda with one parameter. -/
example : Surface 0 Mode.software 1 :=
  Surface.lamMulti span oneUnitParam
    (Surface.var span ⟨0, Nat.zero_lt_succ 0⟩)

/-- Span extraction returns the constructor span. -/
example :
    Surface.spanOf (Surface.unit (scope := 0) (mode := Mode.software) span) = span :=
  rfl

end SmokeTestSurface

end LeanFX.Frontend
