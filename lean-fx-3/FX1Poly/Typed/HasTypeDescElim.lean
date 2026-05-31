import FX1Poly.Typed.HasTypeDesc

/-! # FX1Poly/Typed/HasTypeDescElim — the eliminator-shape SUBSTRATE for the
    description engine: a heterogeneous typed-children telescope over `HasTypeDesc`.

The description engine's formation premise spine `DescTelescope` types EVERY child
at a UNIVERSE CODE (`universeCodeCell levelᵢ flag`): it expresses telescopes of
TYPES — the formation shape, whose output is a universe.  The §11.8.5 non-uniform
seam PAST formation is the ELIMINATOR shape, whose children are TERMS classified
by motive-dependent types (a scrutinee `: Nat`, a motive `: a Π-type`, branches
`: motive-instances`), NOT universes.  The universe-only spine structurally cannot
express that; the eliminator arm needs a premise spine where each child is typed
at an ARBITRARY classifier.

This file carries that substrate over the description engine `HasTypeDesc`:
`DescTermTelescope`, the maximally-general typed-children spine — each child typed
at an arbitrary `headClassifier : RawTerm` that may mention all prior children (it
lives at the cumulatively-extended scope).  An eliminator `gen`-arm consumes this
ONE spine.

## Non-vacuity / faithfulness

* `DescTelescope.toTermTelescope` — the formation spine is an INSTANCE of the
  general term spine: every universe-code-typed telescope IS a term telescope with
  the classifiers chosen to be universe codes.  So the eliminator substrate SUBSUMES
  formation (the eliminator arm reuses this one spine, no separate formation path).
  Term-mode `match` (the propext-free structural form used by
  `DescTelescope.toHasTypeTelescope`), self-recursive only — it treats each
  `headTyped : HasTypeDesc` opaquely, so no mutual block with `HasTypeDesc` is needed.
* `descTermTelescope_heterogeneous` — a genuinely HETEROGENEOUS `[0,1]` telescope
  `[childZero : classifierZero, childOne : classifierOne]` at ARBITRARY classifiers
  (not universe codes), each possibly depending on priors.  The universe-only
  formation spine cannot express this; the general spine accepts it — the
  eliminator-relevant generality, concretely witnessed.

## Rebasing / zero-axiom

Same fixed-`baseScope`, growing-`currentDepth` discipline as
`DescTelescope` (children indexed at a fixed `baseScope`, only the context grows via
`currentDepth`, so `(baseScope+currentDepth)+1 = baseScope+(currentDepth+1)`
definitionally — no cast).  Standalone inductive (`HasTypeDesc` appears only
POSITIVELY in `cons`'s `headTyped`, and is already defined — no mutual block).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The maximally-general typed-children spine for the description engine: a
cumulative dependent telescope of typed TERMS, each typed at an ARBITRARY classifier
provided per `cons` step (which may mention all prior children — it lives at the
extended scope).  The universe formation telescope `DescTelescope` is the instance
where every classifier is a `universeCodeCell`.  Standalone — references the
already-defined `HasTypeDesc` only positively in `cons`'s `headTyped` (no mutual
block); same shift-rebasing discipline as `DescTelescope`. -/
inductive DescTermTelescope (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth)) :
      DescTermTelescope profile context .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headClassifier : RawTerm (baseScope + currentDepth))
      (rest : RawTermChildren restShifts baseScope)
      (headTyped : HasTypeDesc profile context head headClassifier)
      (restTyped :
        DescTermTelescope profile (currentDepth := currentDepth + 1)
          (context.cons head) rest) :
      DescTermTelescope profile context (.childCons head rest)

/-- The formation spine is an INSTANCE of the general term spine: a `DescTelescope`
(every child typed at a universe code) reconstructs as a `DescTermTelescope` with the
classifiers chosen to be those universe codes.  So the eliminator substrate subsumes
formation.  Term-mode `match` (propext-free structural form, mirroring
`DescTelescope.toHasTypeTelescope`); self-recursive only (each `headTyped` is passed
opaquely), so no mutual block with `HasTypeDesc` is needed. -/
theorem DescTelescope.toTermTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (spine : DescTelescope profile context levels flag children) :
    DescTermTelescope profile context children :=
  match spine with
  | .nil context _flag => DescTermTelescope.nil context
  | .cons context head headLevel _restLevels flag rest headTyped restTyped =>
      DescTermTelescope.cons context head (universeCodeCell headLevel flag) rest
        headTyped (DescTelescope.toTermTelescope restTyped)

/-- Genuine generality beyond the universe telescope: a HETEROGENEOUS `[0,1]`
telescope whose children are typed at ARBITRARY classifiers (not universe codes),
each possibly depending on prior children.  This is the shape an eliminator rule
consumes (scrutinee/motive/branches at motive-dependent types) — the universe-only
formation spine cannot express it, but the general spine accepts it. -/
theorem descTermTelescope_heterogeneous
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (childZero : RawTerm scope) (classifierZero : RawTerm scope)
    (childOne : RawTerm (scope + 1)) (classifierOne : RawTerm (scope + 1))
    (typedZero : HasTypeDesc profile context childZero classifierZero)
    (typedOne :
      HasTypeDesc profile (context.cons childZero) childOne classifierOne) :
    DescTermTelescope profile (currentDepth := 0) context
      (RawTermChildren.binderShape childZero childOne) := by
  refine DescTermTelescope.cons (currentDepth := 0) context childZero
    classifierZero (.childCons childOne .childNil) typedZero ?_
  exact DescTermTelescope.cons (currentDepth := 1) (context.cons childZero)
    childOne classifierOne .childNil typedOne
    (DescTermTelescope.nil (currentDepth := 2)
      (context.cons childZero |>.cons childOne))

end FX1Poly.Typed
