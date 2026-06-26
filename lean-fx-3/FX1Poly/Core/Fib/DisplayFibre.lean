import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Core.Fib.UniverseCodeBridge

/-! # FX1Poly/Core/Fib/DisplayFibre — fib-1a: the display fibre + its type-axis indexing

The `type ↠ context` display fibration (fib-1) needs a union-level "Γ ⊢ A type" predicate — the FIBRE over a
context.  That predicate ALREADY EXISTS and is over the SHIPPED kernel judgment (not the formation engine):
`UnionClassifierIsType profile context classifier := ∃ levelExpr flag, HasTypeUnion profile context classifier
(universeCodeCell levelExpr flag)` (`Typed/Metatheory/Validity/HasTypeUnionValidity.lean:80`).  A classifier is a
well-formed type iff it inhabits SOME universe code.  Per the no-remnants rule we REUSE it (no parallel
`IsTypeUnion`); it already carries the fibre-population lemmas `UnionClassifierIsType.ofUniverseCode` /
`.ofBaseTypeRow` / `.ofFormationOutput` (every tabled formation output is a type).

fib-1a's genuinely NEW content is the connection to fib-2: the display FIBRES are INDEXED by the type-axis
universe codes.  A classifier is a well-formed type iff it is typed at SOME bridged type-axis code
`axisCodeToCell code` — so the type axis's standalone universe (fib-2) is exactly the index of the display
fibration's fibres (fib-1).  This is the first `type ↠ context` ⋈ `type ↔ term` cross-connection at `Core/Fib`.

fib-1b lifts the shipped display-map prototype `DisplayMapDecidableFibration` (over the formation engine) onto
this `HasTypeUnion`-level fibre; fib-1c identifies `TypingContext.cons` with the categorical context-extension;
fib-1d supplies the fibred-Π right adjoint and flips `fxFib_hasTypeContextDisplay`.

## Zero-axiom

A reuse of `UnionClassifierIsType` + one `Iff` whose halves repackage the existential's `(levelExpr, flag)`
witness as a `UniverseCode` and back (defeq through `axisCodeToCell`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Typed FX1Poly.Universe

/-- **★ The display fibre is indexed by the type-axis universe codes (fib-1 ⋈ fib-2).**  A classifier is a
well-formed union type (the display fibre `UnionClassifierIsType`) iff it is typed at SOME bridged type-axis
universe code `axisCodeToCell code`.  So the type axis's standalone universe codes (fib-2) ARE the index set of
the display fibration's fibres (fib-1): "Γ ⊢ A type" = "A : Type@code for some axis code".  The two halves
repackage the existential's `(levelExpr, flag)` witness as a `UniverseCode` and back (defeq through
`axisCodeToCell`). -/
theorem unionClassifierIsType_iff_typedAtAxisCode {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    UnionClassifierIsType profile context classifier ↔
      ∃ code : UniverseCode, HasTypeUnion profile context classifier (axisCodeToCell code) := by
  constructor
  · rintro ⟨levelExpr, flag, typed⟩
    exact ⟨{ level := levelExpr, flag := flag }, typed⟩
  · rintro ⟨code, typed⟩
    exact ⟨code.level, code.flag, typed⟩

/-- A bridged type-axis universe code is itself a well-formed union type (the fibre is non-empty at every axis
code) — `axisCodeToCell code : Type@(successor code)` is union-typed, so it inhabits the fibre.  The fib-2
`axisCodeToCell_typedAtSuccessor` read as a fibre-population fact for fib-1. -/
theorem axisCodeToCell_unionClassifierIsType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (code : UniverseCode) :
    UnionClassifierIsType profile context (axisCodeToCell code) :=
  UnionClassifierIsType.ofUniverseCode context code.level code.flag

end FX1Poly.Core.Fib
